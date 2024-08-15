module ram (ram_if.DUT intr);

	reg [intr.ADDR_SIZE-1:0] write_addr, read_addr;
	reg [intr.ADDR_SIZE-1:0] mem [intr.MEM_DEPTH-1:0];



/////////////////////////////////Original Code//////////////////////////////////

/*	
	integer i=0;
	always @(posedge intr.clk,negedge intr.rst_n) begin
		if(~intr.rst_n) begin
			for (i=0; i < intr.MEM_DEPTH; i=i+1) begin 		//memory values should not equal zero following each reset, only Module outputs (and wr/rd addresses).
				mem[i] = 0;
			end
		end
		else if(intr.rx_valid) begin
			case (intr.din[9:8])								//Should use parameter (intr.ADDR_SIZE) instead of actual size
				2'b00: begin
					write_addr <= intr.din[7:0];
					intr.tx_valid <=0;
				end
				2'b01: begin
					mem [write_addr] <= intr.din[7:0];
					intr.tx_valid <=0;
				end	
				2'b10: begin
					read_addr <= intr.din[7:0];
					intr.tx_valid <=0;
				end
				2'b11: begin							//For Code Coverage = 100% -> This branch is moved to default
					intr.dout <= mem[read_addr];
					intr.tx_valid <=1;
				end
			endcase
		end
		else 
			intr.tx_valid =0;
	end
*/
	


/////////////////////////////////Edited Code//////////////////////////////////

	always @(posedge intr.clk,negedge intr.rst_n) begin
		if(~intr.rst_n) begin
			intr.dout <= 0;
			intr.tx_valid <= 0;
			write_addr <= 0;
			read_addr <= 0;
		end
		else if(intr.rx_valid) begin
			case (intr.din[intr.ADDR_SIZE+1:intr.ADDR_SIZE])
				2'b00: begin
					write_addr <= intr.din[intr.ADDR_SIZE-1:0];
					intr.tx_valid <=0;
				end
				2'b01: begin
					mem [write_addr] <= intr.din[intr.ADDR_SIZE-1:0];
					intr.tx_valid <=0;
				end	
				2'b10: begin
					read_addr <= intr.din[intr.ADDR_SIZE-1:0];
					intr.tx_valid <=0;
				end
				default: begin
					intr.dout <= mem[read_addr];
					intr.tx_valid <=1;
				end
			endcase
		end
	end


`ifdef SIM
		//For Visual Clarity
		logic [1:0] signal;
		logic [intr.ADDR_SIZE-1:0] data;
		assign signal = intr.din[intr.ADDR_SIZE+1 : intr.ADDR_SIZE];
		assign data = intr.din[intr.ADDR_SIZE-1 : 0];


	///////////////////////////////////////////////Checking Stable Cases (IDLE)///////////////////////////////////////////////

		//Checks Reset Functionality -on internal signals and outputs
		property reset_asserted;
			@(posedge intr.clk)

			$fell(intr.rst_n) |=> !(intr.dout || intr.tx_valid || write_addr || read_addr);
		endproperty

		//Ensures No memory manipulation when rx_valid is inactive
		property rx_valid_inactive;
			@(posedge intr.clk) disable iff(!intr.rst_n)

			$fell(intr.rx_valid) |=> $stable(mem) && $stable(write_addr) && $stable(read_addr);
		endproperty



	/////////////////////////////////////////////Checking Original Functionality/////////////////////////////////////////////

		//Checks Saving Write Address
		property save_write_addr;
			@(posedge intr.clk) disable iff(!intr.rst_n)

			((signal == 0) && intr.rx_valid) |=> (write_addr == $past(data));
		endproperty

		//Checks Writing Data
		property wr_data;
			@(posedge intr.clk) disable iff(!intr.rst_n)

			((signal == 1) && intr.rx_valid) |=> (mem[write_addr] == $past(data));
		endproperty

		//Checks Saving Read Address
		property save_read_addr;
			@(posedge intr.clk) disable iff(!intr.rst_n)

			((signal == 2) && intr.rx_valid) |=> (read_addr == $past(data));
		endproperty

		//Checks Reading Data
		property rd_data;
			@(posedge intr.clk) disable iff(!intr.rst_n)

			((signal == 3) && intr.rx_valid) |=> (intr.dout == mem[$past(read_addr)]);
		endproperty

		//Checks tx_valid is active if data is ready
		property tx_valid_active;
			@(posedge intr.clk) disable iff(!intr.rst_n)

			((signal == 3) && intr.rx_valid) |=> intr.tx_valid;
		endproperty

		//Checks tx_valid is not active if data is not ready (signal = 3)
		property tx_valid_inactive;
			@(posedge intr.clk) disable iff(!intr.rst_n)

			((signal != 3) && intr.rx_valid) |=> !intr.tx_valid;
		endproperty


		/////////////////////////////////////////////Checking Different Scenarios/////////////////////////////////////////////
/*
		//Checks Normal Write Operation
		property normal_write_op;
			logic [intr.ADDR_SIZE-1:0] data_sva, address;
			@(posedge intr.clk) disable iff(!intr.rst_n)

			//Signal = 0: Saving Address -> Signal = 1: Writing data in that address -> Check: The written data is actually in the location provided in the internal memory
			(((signal == 0) && intr.rx_valid), address = data) ##[1:intr.ADDR_SIZE+5] (((signal == 1) && intr.rx_valid), data_sva = data) |=> (mem[address] == data_sva);
		endproperty

		//Checks Read Operation
		property normal_read_op;
			logic [intr.ADDR_SIZE-1:0] address;
			@(posedge intr.clk) disable iff(!intr.rst_n)

			//Signal = 2: Saving Address -> Signal = 3: Reading data from that address -> Check: The read data is actually the data found at the location provided in the internal memory
			(((signal == 2) && intr.rx_valid), address = data) ##[1:intr.ADDR_SIZE+5] ((signal == 3) && intr.rx_valid) |=> (intr.dout == mem[address]);
		endproperty
*/
		//Checks Writing then Reading from the same location
		/*
		property main_op;
			logic [intr.ADDR_SIZE-1:0] address, content;
			@(posedge intr.clk) disable iff(!intr.rst_n || !intr.rx_valid)

			//Signal = 1: Data (content) is written into a specific location (address) -> signal = 1 would override its content (ignored) -> Signal = 2 and read_addr = previous location (address): Next signal = 3 would read (content)
			((signal == 1), content = data, address = write_addr) ##1 !((signal == 1) && (write_addr == address)) throughout ( (signal == 2) && (data == address) )[->1] ##1 (signal == 3) |=> (intr.dout == content);
		endproperty
		*/


		assertion_reset:	assert property(reset_asserted);
		cover_reset:	  	cover property(reset_asserted);

		assertion_rx_inv: 	assert property(rx_valid_inactive);
		cover_rx_inv:		cover property(rx_valid_inactive);

		assertion_save_wr:	assert property(save_write_addr);
		cover_save_wr:		cover property(save_write_addr);

		assertion_wr_d:		assert property(wr_data);
		cover_wr_d:			cover property(wr_data);

		assertion_save_rd:	assert property(save_read_addr);
		cover_save_rd:		cover property(save_read_addr);

		assertion_rd_d:		assert property(rd_data);
		cover_rd_d:			cover property(rd_data);

		assertion_tx_a:		assert property(tx_valid_active);
		cover_tx_a:			cover property(tx_valid_active);

		assertion_tx_in:	assert property(tx_valid_inactive);
		cover_tx_in:		cover property(tx_valid_inactive);
/*
		assertion_wr_op: 	assert property(normal_write_op);
		cover_wr_op: 		cover property(normal_write_op);

		assertion_rd_op: 	assert property(normal_read_op);
		cover_rd_op: 		cover property(normal_read_op);
/*
		assertion_main: 	assert property(main_op);
		cover_main: 		cover property(main_op);
*/
`endif

endmodule