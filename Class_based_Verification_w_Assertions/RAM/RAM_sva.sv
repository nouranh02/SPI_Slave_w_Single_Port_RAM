module RAM_sva(clk, rst_n, rx_valid, din, tx_valid, dout, mem, wr_addr, rd_addr);

	//Parameters
	parameter ADDR_SIZE = 8;
	parameter MEM_DEPTH = 256;

	//I/O Ports of DUT
	input clk, rst_n, rx_valid, tx_valid;
	input [ADDR_SIZE+1:0] din;


	//Internal Signals of DUT
	input [ADDR_SIZE-1:0] wr_addr, rd_addr, dout;
	input [ADDR_SIZE-1:0] mem [MEM_DEPTH-1:0];

	//For Visual Clarity
	logic [1:0] signal;
	logic [ADDR_SIZE-1:0] data;
	assign signal = din[ADDR_SIZE+1 : ADDR_SIZE];
	assign data = din[ADDR_SIZE-1 : 0];


///////////////////////////////////////////////Checking Stable Cases (IDLE)///////////////////////////////////////////////

	//Checks Reset Functionality -on internal signals and outputs
	property reset_asserted;
		@(posedge clk)

		$fell(rst_n) |=> !(dout || tx_valid || wr_addr || rd_addr);
	endproperty

	//Ensures No memory manipulation when rx_valid is inactive
	property rx_valid_inactive;
		@(posedge clk) disable iff(!rst_n)

		$fell(rx_valid) |=> $stable(mem) && $stable(wr_addr) && $stable(rd_addr);
	endproperty



/////////////////////////////////////////////Checking Original Functionality/////////////////////////////////////////////

	//Checks Saving Write Address
	property save_wr_addr;
		logic [ADDR_SIZE-1:0] data_old;
		@(posedge clk) disable iff(!rst_n || !rx_valid)

		(signal == 0, data_old = data) |=> (wr_addr == data_old);
	endproperty

	//Checks Writing Data
	property wr_data;
		logic [ADDR_SIZE-1:0] data_old;
		@(posedge clk) disable iff(!rst_n || !rx_valid)

		(signal == 1, data_old = data) |=> (mem[wr_addr] == data_old);
	endproperty

	//Checks Saving Read Address
	property save_rd_addr;
		logic [ADDR_SIZE-1:0] data_old;
		@(posedge clk) disable iff(!rst_n || !rx_valid)

		(signal == 2, data_old = data) |=> (rd_addr == data_old);
	endproperty

	//Checks Reading Data
	property rd_data;
		logic [ADDR_SIZE-1:0] rd_addr_old;
		@(posedge clk) disable iff(!rst_n || !rx_valid)

		(signal == 3, rd_addr_old = rd_addr) |=> (dout == mem[rd_addr_old]);
	endproperty

	//Checks tx_valid is active if data is ready
	property tx_valid_active;
		@(posedge clk) disable iff(!rst_n || !rx_valid)

		(signal == 3) |=> tx_valid;
	endproperty

	//Checks tx_valid is not active if data is not ready (signal = 3)
	property tx_valid_inactive;
		@(posedge clk) disable iff(!rst_n || !rx_valid)

		!(signal == 3) |=> !tx_valid;
	endproperty


	/////////////////////////////////////////////Checking Different Scenarios/////////////////////////////////////////////

	//Checks Normal Write Operation
	property normal_write_op;
		logic [ADDR_SIZE-1:0] address, content;
		@(posedge clk) disable iff(!rst_n || !rx_valid)

		//Signal = 0: Saving Address -> Signal = 1: Writing data in that address -> Check: The written data is actually in the location provided in the internal memory
		(signal == 0, address = data) ##[1:2] (signal == 1, content = data) |=> (mem[address] == content);
	endproperty

	//Checks Read Operation
	property normal_read_op;
		logic [ADDR_SIZE-1:0] address, content;
		@(posedge clk) disable iff(!rst_n || !rx_valid)

		//Signal = 2: Saving Address -> Signal = 3: Reading data from that address -> Check: The read data is actually the data found at the location provided in the internal memory
		(signal == 2, address = data) ##[1:2] (signal == 3) |=> (dout == mem[address]);
	endproperty

	//Checks Writing then Reading from the same location
	property main_op;
		logic [ADDR_SIZE-1:0] address, content;
		@(posedge clk) disable iff(!rst_n || !rx_valid)

		//Signal = 1: Data (content) is written into a specific location (address) -> signal = 1 would override its content (ignored) -> Signal = 2 and rd_addr = previous location (address): Next signal = 3 would read (content)
		((signal == 1), content = data, address = wr_addr) ##1 (signal !== 1) throughout ( (signal == 2) && (rd_addr == address) )[->1] ##1 (signal == 3) |=> (dout == content);
	endproperty



	assertion_reset:	assert property(reset_asserted);
	cover_reset:	  	cover property(reset_asserted);

	assertion_rx_inv: 	assert property(rx_valid_inactive);
	cover_rx_inv:		cover property(rx_valid_inactive);

	assertion_save_wr:	assert property(save_wr_addr);
	cover_save_wr:		cover property(save_wr_addr);

	assertion_wr_d:		assert property(wr_data);
	cover_wr_d:			cover property(wr_data);

	assertion_save_rd:	assert property(save_rd_addr);
	cover_save_rd:		cover property(save_rd_addr);

	assertion_rd_d:		assert property(rd_data);
	cover_rd_d:			cover property(rd_data);

	assertion_tx_a:		assert property(tx_valid_active);
	cover_tx_a:			cover property(tx_valid_active);

	assertion_tx_in:	assert property(tx_valid_inactive);
	cover_tx_in:		cover property(tx_valid_inactive);

	assertion_wr_op: 	assert property(normal_write_op);
	cover_wr_op: 		cover property(normal_write_op);

	assertion_rd_op: 	assert property(normal_read_op);
	cover_rd_op: 		cover property(normal_read_op);

	assertion_main: 	assert property(main_op);
	cover_main: 		cover property(main_op);

endmodule