module slave_sva(MOSI,SS_n,clk,rst_n,tx_valid,tx_data,rx_data,rx_valid,MISO,cs,ns);

	//User-defined data_types and Parameters 
	typedef enum logic [2:0] {IDLE, READ_DATA, READ_ADD, CHK_CMD, WRITE, WAIT_WR, WAIT_RD, WAIT_RD2} state_e;
	parameter ADDR_SIZE = 8;

	//I/O Ports of DUT
	input clk, rst_n, SS_n, MOSI, tx_valid, rx_valid, MISO;
	input [ADDR_SIZE-1:0] tx_data;
	input [ADDR_SIZE+1:0] rx_data;

	//Internal Signals of DUT
	input [2:0] cs, ns;

	//For Visual Clarity
	state_e cs_sva, ns_sva;
	assign cs_sva = state_e'(cs);
	assign ns_sva = state_e'(ns);



///////////////////////////////////////////////Checking Stable Cases (IDLE)///////////////////////////////////////////////

	//Checks rst_n Functionality - Output Values and State Transitions
	property reset_asserted;
		@(posedge clk)

		!rst_n |-> !(rx_valid || rx_data || MISO) && (cs_sva == IDLE);
	endproperty

	//Checks SS_n Functionality - State Transitions
	property SS_inactive;
		@(posedge clk) disable iff(!rst_n)

		$rose(SS_n) |=> (cs_sva == IDLE);
	endproperty



/////////////////////////////////////////////Checking Original Functionality/////////////////////////////////////////////

	/////////////////////////////////////////Checking State Transitions

	//Slave must always go from IDLE to CHK_CMD
	property CHK_first;
		@(posedge clk) disable iff(!rst_n)

		$fell(SS_n) |=> (cs_sva == CHK_CMD);
	endproperty

	//Slave must always go from CHK_CMD to WAIT_WR if 1st MOSI bit = 0
	property CHK_WR;
		@(posedge clk) disable iff(!rst_n)

		$fell(SS_n) ##1 (~MOSI && ~SS_n) |=> (cs_sva == WAIT_WR);
	endproperty

	//Slave must always go from CHK_CMD to WAIT_RD if 1st MOSI bit = 1
	property CHK_RD;
		@(posedge clk) disable iff(!rst_n)

		$fell(SS_n) ##1 (MOSI && ~SS_n) |=> (cs_sva == WAIT_RD);
	endproperty



	//MOSI = 0x
	property MOSI_wr;
		@(posedge clk) disable iff(!rst_n)

		$fell(SS_n) ##1 (~MOSI && ~SS_n)[*2] |=> (cs_sva == WRITE);
	endproperty

	//MOSI = 1x
	property MOSI_rd;
		@(posedge clk) disable iff(!rst_n)

		$fell(SS_n) ##1 (MOSI && ~SS_n)[*2] |=> (cs_sva == WAIT_RD2);
	endproperty

	//MOSI = 10
	property MOSI_rd_add;
		@(posedge clk) disable iff(!rst_n)

		( (cs_sva == READ_DATA) throughout SS_n[->1] ) ##[1:5] $fell(SS_n) ##1 (MOSI && ~SS_n)[*2] ##1 (~MOSI && ~SS_n) |=> (cs_sva == READ_ADD);
	endproperty

	//MOSI = 11
	property MOSI_rd_data;
		@(posedge clk) disable iff(!rst_n)

		( (cs_sva == READ_ADD) throughout SS_n[->1] ) ##[1:5] $fell(SS_n) ##1 (MOSI && ~SS_n)[*3] |=> (cs_sva == READ_DATA);
	endproperty



	//(READ_ADD -> READ_ADD) or (READ_DATA -> READ_DATA) must not occur
	property no_add_add;
		@(posedge clk) disable iff(!rst_n)

		$fell(SS_n) ##1 (!SS_n)[*3] ##1 (cs_sva == READ_ADD)[*1:$] ##1 (SS_n) |=> ( (cs_sva != READ_ADD) throughout (cs_sva == READ_DATA)[->1] );
	endproperty

	property no_data_data;
		@(posedge clk) disable iff(!rst_n)

		$fell(SS_n) ##1 (!SS_n)[*3] ##1 (cs_sva == READ_DATA)[*1:$] ##1 (SS_n) |=> ( (cs_sva != READ_DATA) throughout (cs_sva == READ_ADD)[->1] );
	endproperty




	/////////////////////////////////////////Checking Outputs

	/////////////////rx_data & rx_valid
	property rx;
		logic [ADDR_SIZE+1:0] data_sva = 0;
		@(posedge clk) disable iff(!rst_n)

		$fell(SS_n) ##1 (!SS_n) ##1 ( ((cs != IDLE) && !SS_n), data_sva = {data_sva[ADDR_SIZE:0], MOSI} )[*(ADDR_SIZE+2)] |=> ( (rx_data == data_sva) && rx_valid);
	endproperty

	//rx_data @(rx_valid == 1) in WRITE state must start with 00 or 01
	property rx_wr;
		@(posedge clk) disable iff(!rst_n)

		(rx_valid && (cs_sva == WRITE)) |-> ( (rx_data[ADDR_SIZE+1:ADDR_SIZE] == 2'b00) || (rx_data[ADDR_SIZE+1:ADDR_SIZE] == 2'b01) );
	endproperty

	//rx_data @(rx_valid == 1) in READ_ADD state must start with 10
	property rx_rd_add;
		@(posedge clk) disable iff(!rst_n)

		(rx_valid && (cs_sva == READ_ADD)) |-> (rx_data[ADDR_SIZE+1:ADDR_SIZE] == 2'b10);
	endproperty

	//rx_data @(rx_valid == 1) in READ_DATA state must start with 11
	property rx_rd_data;
		@(posedge clk) disable iff(!rst_n)

		(rx_valid && (cs_sva == READ_DATA)) |-> (rx_data[ADDR_SIZE+1:ADDR_SIZE] == 2'b11);
	endproperty

	//rx_valid cannot be high if tx_valid is high
	property rx_tx;
		@(posedge clk) disable iff(!rst_n)

		($rose(tx_valid) && (cs == READ_DATA)) |=> (~rx_valid) throughout (~tx_valid || (cs != READ_DATA))[->1];
	endproperty

	//rx_valid cannot be high at any checking state
	property rx_chk;
		@(posedge clk) disable iff(!rst_n)

		~( (cs == WRITE) || (cs == READ_ADD) || (cs == READ_DATA) ) |-> (~rx_valid);
	endproperty


	/////////////////MISO
	property tx;
		logic [ADDR_SIZE-1:0] data_sva = 0;
		int i = 0;
		@(posedge clk) disable iff(!rst_n || SS_n || $fell(tx_valid, @(negedge clk)) )

		( ( $rose(tx_valid) && (cs_sva == READ_DATA) ), data_sva = tx_data) |=> ((MISO == data_sva[ADDR_SIZE-1-i]), i++)[*(ADDR_SIZE)];
	endproperty


	//MISO cannot be high at any state other than READ_DATA
	property MISO_rd_only;
		@(posedge clk) disable iff(!rst_n || SS_n)

		~(cs_sva == READ_DATA) |-> (~MISO);
	endproperty






	assertion_reset_asserted:		assert property(reset_asserted);
	cover_reset_asserted:	  		cover property(reset_asserted);

	assertion_SS_inactive:			assert property(SS_inactive);
	cover_SS_inactive:				cover property(SS_inactive);

	assertion_CHK_first:			assert property(CHK_first);
	cover_CHK_first:				cover property(CHK_first);

	assertion_CHK_WR:				assert property(CHK_WR);
	cover_CHK_WR:					cover property(CHK_WR);

	assertion_CHK_RD:				assert property(CHK_RD);
	cover_CHK_RD:					cover property(CHK_RD);

	assertion_MOSI_wr:				assert property(MOSI_wr);
	cover_MOSI_wr:					cover property(MOSI_wr);

	assertion_MOSI_rd:				assert property(MOSI_rd);
	cover_MOSI_rd:					cover property(MOSI_rd);

	assertion_MOSI_rd_add:			assert property(MOSI_rd_add);
	cover_MOSI_rd_add:				cover property(MOSI_rd_add);

	assertion_MOSI_rd_data:			assert property(MOSI_rd_data);
	cover_MOSI_rd_data:				cover property(MOSI_rd_data);

	assertion_no_add_add:			assert property(no_add_add);
	cover_no_add_add:				cover property(no_add_add);

	assertion_no_data_data:			assert property(no_data_data);
	cover_no_data_data:				cover property(no_data_data);

	assertion_rx:					assert property(rx);
	cover_rx:						cover property(rx);

	assertion_rx_wr:				assert property(rx_wr);
	cover_rx_wr:					cover property(rx_wr);

	assertion_rx_rd_add:			assert property(rx_rd_add);
	cover_rx_rd_add:				cover property(rx_rd_add);

	assertion_rx_rd_data:			assert property(rx_rd_data);
	cover_rx_rd_data:				cover property(rx_rd_data);

	assertion_rx_tx:				assert property(rx_tx);
	cover_rx_tx:					cover property(rx_tx);

	assertion_rx_chk:				assert property(rx_chk);
	cover_rx_chk:					cover property(rx_chk);

	assertion_tx:					assert property(tx);
	cover_tx:						cover property(tx);

	assertion_MISO_rd_only:			assert property(MISO_rd_only);
	cover_MISO_rd_only:				cover property(MISO_rd_only);

endmodule