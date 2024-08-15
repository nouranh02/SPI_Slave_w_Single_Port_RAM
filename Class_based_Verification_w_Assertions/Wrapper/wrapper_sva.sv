module wrapper_sva(MOSI,MISO,SS_n,clk,rst_n,mem,cs,tx_valid,tx_data,rx_valid,rx_data);

	//User-defined data_types and Parameters 
	typedef enum logic [2:0] {IDLE, READ_DATA, READ_ADD, CHK_CMD, WRITE, WAIT_WR, WAIT_RD, WAIT_RD2} state_e;
	parameter ADDR_SIZE = 8;
	parameter MEM_DEPTH = 256;

	//I/O Ports of DUT
	input clk, rst_n, SS_n, MOSI, MISO;

	//Internal Signals of DUT
	input [ADDR_SIZE-1:0] mem [MEM_DEPTH-1:0];
	input [ADDR_SIZE+1:0] rx_data;
	input [ADDR_SIZE-1:0] tx_data;
	input rx_valid, tx_valid;
	input [2:0] cs;

	//For Visual Clarity
	state_e cs_sva;
	assign cs_sva = state_e'(cs);


	/*
	Critical Conditions to Check (Memory Contents must not get corrupted in these cases):
		- Following rst_n assertion
		- At states other than (WRITE, READ_ADD)
		- If rx_valid is not high


	Basic Function of SPI (Slave and Ram) is checked in their separate assertions
	Output is Checked against Golden Model
	*/

	
	property reset_asserted;
		@(posedge clk)

		!rst_n |=> (~MISO && $stable(mem));
	endproperty

	property no_wr_op;
		@(posedge clk) disable iff(!rst_n)

		!((cs_sva == WRITE) || (cs_sva == READ_ADD)) |=> $stable(mem);
	endproperty

	property SS_inactive;
		@(posedge clk) disable iff(!rst_n)

		(SS_n) |=> ##1 $stable(mem);
	endproperty



	
	/////////////Checking Output Behavior
	
	property MISO_no_rd;
		@(posedge clk) disable iff(!rst_n)

		!(cs_sva == READ_DATA) |=> ~MISO;
	endproperty

	property MISO_tx_inactive;
		@(posedge clk) disable iff(!rst_n)

		!(tx_valid) |=> ~MISO;
	endproperty
/*
	property MISO_mem;
		bit [ADDR_SIZE-1:0] address;
		int i = 0;
		@(posedge clk) disable iff(!rst_n || ($fell(rx_data[ADDR_SIZE+1], @(negedge clk)) && $fell(rx_data[ADDR_SIZE], @(negedge clk))) )

		($rose(rx_valid) && cs_sva == READ_ADD, address = rx_data) ##[1:$] (cs != READ_ADD) throughout (~SS_n && (cs_sva == READ_DATA))[->1] ##[1:$] (tx_valid) |=> ((MISO == mem[address][ADDR_SIZE-1-i]), i++)[*(ADDR_SIZE)];
	endproperty

	property MOSI_mem;
		bit [ADDR_SIZE-1:0] address;
		int i = 0;
		@(posedge clk) disable iff(!rst_n)

		($rose(rx_valid) && cs_sva == WRITE && (rx_data[ADDR_SIZE+1:ADDR_SIZE] == 2'b10)) |=> !$stable(mem);
	endproperty
*/


	assertion_reset_asserted:		assert property(reset_asserted);
	cover_reset_asserted:	  		cover property(reset_asserted);

	assertion_no_wr_op:				assert property(no_wr_op);
	cover_no_wr_op:	  				cover property(no_wr_op);

	assertion_SS_inactive:			assert property(SS_inactive);
	cover_SS_inactive:	  			cover property(SS_inactive);

	assertion_MISO_no_rd:			assert property(MISO_no_rd);
	cover_SS_MISO_no_rd:			cover property(MISO_no_rd);

	assertion_MISO_tx_inactive:		assert property(MISO_tx_inactive);
	cover_MISO_tx_inactive:			cover property(MISO_tx_inactive);
/*
	assertion_MISO_mem:				assert property(MISO_mem);
	cover_MISO_mem:					cover property(MISO_mem);

	assertion_MOSI_mem:				assert property(MOSI_mem);
	cover_MOSI_mem:					cover property(MOSI_mem);
*/
endmodule