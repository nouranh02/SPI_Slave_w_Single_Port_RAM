module slave(slave_if.DUT intr);

	parameter IDLE = 3'b000;
	parameter READ_DATA = 3'b001;
	parameter READ_ADD = 3'b010;
	parameter CHK_CMD = 3'b011;
	parameter WRITE = 3'b100;
	parameter WAIT_WR = 3'b101;
	parameter WAIT_RD = 3'b110;
	parameter WAIT_RD2 = 3'b111;
	reg [2:0] cs,ns;
	reg start_to_give,start_to_take;
	reg [intr.ADDR_SIZE-1:0] temp;				//param
	reg rd_addr_received;
	reg [3:0] i = 0 ;
	reg [3:0] j = 0;

	reg [intr.ADDR_SIZE:0] rx_temp;


/////////////////////////////////Original Code//////////////////////////////////////
/*

	always@(posedge intr.clk or negedge intr.rst_n)	begin
		if(~intr.rst_n)	begin
			cs <= IDLE ;
		end
		else	begin
			cs <= ns ;
		end
	end
	//Next state logic
	always@(cs,intr.SS_n,intr.MOSI)	begin
		case(cs)
			IDLE:
				if(intr.SS_n)		begin
					ns <= IDLE ;
				end
				else	begin
					ns <= CHK_CMD ;
				end
			READ_DATA:
				if(~intr.SS_n &&( start_to_take || start_to_give ))	begin
					ns <= READ_DATA ;
				end
				else	begin
					ns <= IDLE ;
				end
			READ_ADD:
				if(~intr.SS_n && start_to_give)	begin
					ns <= READ_ADD ;
				end
				else	begin
					ns <= IDLE ;
				end
			CHK_CMD:
				if( (~intr.SS_n) && (intr.MOSI == 1) && rd_addr_received )	begin
					ns <= READ_DATA ;
				end
				else if( (~intr.SS_n) && (intr.MOSI == 1) )	begin
					ns <= READ_ADD ;
				end
				else if ( (~intr.SS_n) && (intr.MOSI == 0) )	begin
					ns <= WRITE ;
				end
				else if (intr.SS_n)	begin
					ns <= IDLE ;
				end
			WRITE:
				if(~intr.SS_n && start_to_give)	begin
					ns <= WRITE ;
				end
				else	begin
					ns <= IDLE ;
				end

			default: ns <= IDLE;
		endcase
	end

	always @(posedge intr.clk) begin
		if (cs == READ_ADD)
			rd_addr_received=1;
		else if (cs == READ_DATA)
			rd_addr_received=0;
	end

	always@(posedge intr.clk)	begin
		if (start_to_give ==1 && ~intr.SS_n)	begin
			intr.rx_data <= {intr.rx_data[intr.ADDR_SIZE:0],intr.MOSI};		//param
			if (i==intr.ADDR_SIZE+1) begin 					//param
				i<=0;
				intr.rx_valid =1;
				start_to_give <= 0;
			end
			else  begin
				i <= i + 1 ;
				intr.rx_valid <= 0;
			end
		end
		else begin
			intr.rx_valid <=0;
			if((cs == CHK_CMD) && (intr.SS_n == 0))	
				start_to_give <= 1;
		end
	end

	

	always@ (posedge intr.tx_valid)begin
		start_to_take <=1;
		temp <= intr.tx_data;
	end

	always@(start_to_take,posedge intr.clk)	begin
		if (start_to_take==1 && ~intr.SS_n) begin
			intr.MISO <= temp[0];
			temp <= {1'b0,temp[intr.ADDR_SIZE-1:1]};			//param
			if (j == intr.ADDR_SIZE-1)	begin 				//param
				start_to_take <= 0 ;
				j <= 0;
			end
			else begin
			j <= j + 1 ;
			end
		end
	end
*/
////////////////////////////////////////////////////////////////////////////////////


/////////////////////////////////Edited Code////////////////////////////////////////

	always@(posedge intr.clk or negedge intr.rst_n)	begin
		if(~intr.rst_n)	begin
			cs <= IDLE ;
		end
		else	begin
			cs <= ns ;
		end
	end
	//Next state logic
	always@(cs,intr.SS_n,intr.MOSI)	begin
		case(cs)
			IDLE:
				if(intr.SS_n)		begin
					ns <= IDLE ;
				end
				else	begin
					ns <= CHK_CMD ;
				end
			READ_DATA:
				if(intr.SS_n) 	begin
					ns <= IDLE;
				end
				else if( start_to_take )	begin
					ns <= READ_DATA ;
				end
			READ_ADD:
				if(~intr.SS_n && start_to_give)	begin
					ns <= READ_ADD ;
				end
				else if(intr.SS_n)	begin
					ns <= IDLE ;
				end
			CHK_CMD:
				if(intr.SS_n) ns <= IDLE;
				else begin
					if(intr.MOSI) ns <= WAIT_RD;
					else ns <= WAIT_WR;
				end
			WAIT_WR:
				if(intr.SS_n || intr.MOSI) ns <= IDLE;
				else ns <= WRITE;
			WAIT_RD:
				if(intr.SS_n || ~intr.MOSI) ns <= IDLE;
				else ns <= WAIT_RD2;
			WAIT_RD2:
				if(intr.SS_n) ns <= IDLE;
				else begin
					if(rd_addr_received && intr.MOSI) ns <= READ_DATA;
					else if(~rd_addr_received && ~intr.MOSI) ns <= READ_ADD;
					else ns <= IDLE;
				end
			WRITE:
				if(~intr.SS_n && start_to_give)	begin
					ns <= WRITE ;
				end
				else if(intr.SS_n)	begin
					ns <= IDLE ;
				end

			default: ns <= IDLE;
		endcase
	end

	always @(posedge intr.clk or negedge intr.rst_n) begin
		if(cs == IDLE) begin
			rx_temp <= 0;
			intr.rx_valid <= 0;
			intr.MISO <= 0;
			start_to_give <= 0;
			start_to_take <= 0;
			temp <= 0;
		end
	end

	always @(posedge intr.clk or negedge intr.rst_n) begin
		if(!intr.rst_n) rd_addr_received=0;
		else begin
			if (cs == READ_ADD)
				rd_addr_received=1;
			else if (cs == READ_DATA)
				rd_addr_received=0;
		end
	end

	always@(posedge intr.clk or negedge intr.rst_n) begin
		if(~intr.rst_n || intr.SS_n) begin
			rx_temp <= 0;
			intr.rx_valid <= 0;
			i <= 0;
		end
		else begin
			if (start_to_give)	begin
				rx_temp <= {rx_temp[intr.ADDR_SIZE-1:0],intr.MOSI};	//param
				if (i==intr.ADDR_SIZE) begin 					//param
					i<=0;
					start_to_give <= 0;
					if(intr.tx_valid && (cs == READ_DATA)) intr.rx_valid <= 0;
					else intr.rx_valid <= 1;
				end
				else  begin
					i <= i + 1 ;
					intr.rx_valid <= 0;
				end
			end
			else begin
				intr.rx_valid <= 0;
				if( ((cs == WAIT_WR) && ~intr.MOSI) || ((cs == WAIT_RD) && intr.MOSI) ) begin
					start_to_give <= 1;
					i <= 0;
				end
			end
		end
	end

	always@ (posedge intr.tx_valid or negedge intr.rst_n)begin
		if(~intr.rst_n) begin
			temp <= 0;
			start_to_take <=0;
			rd_addr_received <= 0;
		end
		else /*if(cs == READ_DATA)*/ begin
			start_to_take <=1;
			temp <= intr.tx_data;
		end
		/*else start_to_take <= 0;*/
	end

	always@(posedge intr.clk or negedge intr.rst_n)	begin
		if(~intr.rst_n || intr.SS_n) begin
			intr.MISO <= 0;
			start_to_take <= 0;
			j <= 0;
		end
		else begin
			if (intr.tx_valid && start_to_take) begin
				intr.MISO <= temp[intr.ADDR_SIZE-1];
				temp <= {temp[intr.ADDR_SIZE-2:0], 1'b0};	//param
				if (j == intr.ADDR_SIZE)	begin 			//param
					start_to_take <= 0 ;
					j <= 0;
				end
				else begin
					j <= j + 1 ;
				end
			end
			else begin
				intr.MISO <= 0;
				start_to_take <= 0;
				j <= 0;
			end
		end
	end


	assign intr.rx_data = ((cs == READ_ADD) || (cs == READ_DATA)) ? {1'b1, rx_temp} : (cs == WRITE) ? {1'b0, rx_temp} : 0;

////////////////////////////////////////////////////////////////////////////////////

`ifdef SIM
	typedef enum logic [2:0] {IDLE_, READ_DATA_, READ_ADD_, CHK_CMD_, WRITE_, WAIT_WR_, WAIT_RD_, WAIT_RD2_} state_e;

	//For Visual Clarity
	state_e cs_sva, ns_sva;
	assign cs_sva = state_e'(cs);
	assign ns_sva = state_e'(ns);


///////////////////////////////////////////////Checking Stable Cases (IDLE)///////////////////////////////////////////////

	//Checks rst_n Functionality - Output Values and State Transitions
	property reset_asserted;
		@(posedge intr.clk)

		$fell(intr.rst_n) |-> !(intr.rx_valid || intr.rx_data || intr.MISO) && (cs_sva == IDLE_);
	endproperty

	//Checks SS_n Functionality - State Transitions
	property SS_inactive;
		@(posedge intr.clk) disable iff(!intr.rst_n)

		$rose(intr.SS_n) |=> (cs_sva == IDLE_);
	endproperty



/////////////////////////////////////////////Checking Original Functionality/////////////////////////////////////////////

	/////////////////////////////////////////Checking State Transitions

	//Slave must always go from IDLE to CHK_CMD
	property CHK_first;
		@(posedge intr.clk) disable iff(!intr.rst_n)

		$fell(intr.SS_n) |=> (cs_sva == CHK_CMD_);
	endproperty

	//Slave must always go from CHK_CMD to WAIT_WR if 1st MOSI bit = 0
	property CHK_WR;
		@(posedge intr.clk) disable iff(!intr.rst_n)

		$fell(intr.SS_n) ##1 (~intr.MOSI && ~intr.SS_n) |=> (cs_sva == WAIT_WR_);
	endproperty

	//Slave must always go from CHK_CMD to WAIT_RD if 1st MOSI bit = 1
	property CHK_RD;
		@(posedge intr.clk) disable iff(!intr.rst_n)

		$fell(intr.SS_n) ##1 (intr.MOSI && ~intr.SS_n) |=> (cs_sva == WAIT_RD_);
	endproperty



	//MOSI = 0x
	property MOSI_wr;
		@(posedge intr.clk) disable iff(!intr.rst_n)

		$fell(intr.SS_n) ##1 (~intr.MOSI && ~intr.SS_n)[*2] |=> (cs_sva == WRITE_);
	endproperty

	//MOSI = 1x
	property MOSI_rd;
		@(posedge intr.clk) disable iff(!intr.rst_n)

		$fell(intr.SS_n) ##1 (intr.MOSI && ~intr.SS_n)[*2] |=> (cs_sva == WAIT_RD2_);
	endproperty

	//MOSI = 10
	property MOSI_rd_add;
		@(posedge intr.clk) disable iff(!intr.rst_n)

		( (cs_sva == READ_DATA_) throughout intr.SS_n[->1] ) ##[1:5] $fell(intr.SS_n) ##1 (intr.MOSI && ~intr.SS_n)[*2] ##1 (~intr.MOSI && ~intr.SS_n) |=> (cs_sva == READ_ADD_);
	endproperty

	//MOSI = 11
	property MOSI_rd_data;
		@(posedge intr.clk) disable iff(!intr.rst_n)

		( (cs_sva == READ_ADD_) throughout intr.SS_n[->1] ) ##[1:5] $fell(intr.SS_n) ##1 (intr.MOSI && ~intr.SS_n)[*3] |=> (cs_sva == READ_DATA_);
	endproperty



	//(READ_ADD -> READ_ADD) or (READ_DATA -> READ_DATA) must not occur
	property no_add_add;
		@(posedge intr.clk) disable iff(!intr.rst_n)

		$fell(intr.SS_n) ##1 (!intr.SS_n)[*3] ##1 (cs_sva == READ_ADD_)[*1:$] ##1 (intr.SS_n) |=> ( (cs_sva != READ_ADD_) throughout (cs_sva == READ_DATA_)[->1] );
	endproperty

	property no_data_data;
		@(posedge intr.clk) disable iff(!intr.rst_n)

		$fell(intr.SS_n) ##1 (!intr.SS_n)[*3] ##1 (cs_sva == READ_DATA_)[*1:$] ##1 (intr.SS_n) |=> ( (cs_sva != READ_DATA_) throughout (cs_sva == READ_ADD_)[->1] );
	endproperty




	/////////////////////////////////////////Checking Outputs

	/////////////////rx_data & rx_valid
	/*
	property rx;
		logic [intr.ADDR_SIZE+1:0] data_sva = 0;
		@(posedge intr.clk) disable iff(!intr.rst_n || (intr.tx_valid && (cs_sva == READ_DATA_)))

		$fell(intr.SS_n) ##1 (!intr.SS_n) ##1 ( ((cs != IDLE_) && !intr.SS_n), data_sva = {data_sva[intr.ADDR_SIZE:0], intr.MOSI} )[*(intr.ADDR_SIZE+2)] |=> ( (intr.rx_data == data_sva) && intr.rx_valid);
	endproperty
	*/
	//rx_data @(rx_valid == 1) in WRITE state must start with 00 or 01
	property rx_wr;
		@(posedge intr.clk) disable iff(!intr.rst_n)

		(intr.rx_valid && (cs_sva == WRITE_)) |-> ( (intr.rx_data[intr.ADDR_SIZE+1:intr.ADDR_SIZE] == 2'b00) || (intr.rx_data[intr.ADDR_SIZE+1:intr.ADDR_SIZE] == 2'b01) );
	endproperty

	//rx_data @(rx_valid == 1) in READ_ADD state must start with 10
	property rx_rd_add;
		@(posedge intr.clk) disable iff(!intr.rst_n)

		(intr.rx_valid && (cs_sva == READ_ADD_)) |-> (intr.rx_data[intr.ADDR_SIZE+1:intr.ADDR_SIZE] == 2'b10);
	endproperty

	//rx_data @(rx_valid == 1) in READ_DATA state must start with 11
	property rx_rd_data;
		@(posedge intr.clk) disable iff(!intr.rst_n)

		(intr.rx_valid && (cs_sva == READ_DATA_)) |-> (intr.rx_data[intr.ADDR_SIZE+1:intr.ADDR_SIZE] == 2'b11);
	endproperty

	//rx_valid cannot be high if tx_valid is high
	property rx_tx;
		@(posedge intr.clk) disable iff(!intr.rst_n)

		($rose(intr.tx_valid) && (cs == READ_DATA_)) |=> (~intr.rx_valid) throughout (~intr.tx_valid || (cs != READ_DATA))[->1];
	endproperty

	//rx_valid cannot be high at any checking state
	property rx_chk;
		@(posedge intr.clk) disable iff(!intr.rst_n)

		~( (cs == WRITE_) || (cs == READ_ADD_) || (cs == READ_DATA_) ) |-> (~intr.rx_valid);
	endproperty


	/////////////////MISO
/*
	property tx;
		logic [intr.ADDR_SIZE-1:0] data_sva = 0;
		int i = 0;
		@(posedge intr.clk) disable iff(!intr.rst_n || intr.SS_n || $fell(intr.tx_valid, @(negedge intr.clk)) )

		( ( $rose(intr.tx_valid) && (cs_sva == READ_DATA_) ), data_sva = intr.tx_data) |=> ((intr.MISO == data_sva[intr.ADDR_SIZE-1-i]), i++)[*(intr.ADDR_SIZE)];
	endproperty
*/

	//MISO cannot be high at any state other than READ_DATA
	property MISO_rd_only;
		@(posedge intr.clk) disable iff(!intr.rst_n || intr.SS_n)

		~(cs_sva == READ_DATA_) |-> (~intr.MISO);
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
/*
	assertion_rx:					assert property(rx);
	cover_rx:						cover property(rx);
*/
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
/*
	assertion_tx:					assert property(tx);
	cover_tx:						cover property(tx);
*/
	assertion_MISO_rd_only:			assert property(MISO_rd_only);
	cover_MISO_rd_only:				cover property(MISO_rd_only);
`endif


endmodule