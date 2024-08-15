import RAM_pkg::*;


module RAM_tb;
	//Parameters
	parameter MEM_DEPTH = 256;
	parameter ADDR_SIZE = 8;

	//Inputs to DUT
	bit clk, rst_n, rx_valid;
	logic [ADDR_SIZE+1:0] din;

	//Outputs of DUT
	bit tx_valid;
	logic [ADDR_SIZE-1:0] dout;

	//Associative Array for RAM
	logic [ADDR_SIZE-1:0] RAM_assoc [logic [ADDR_SIZE-1:0]];

	//Internal Signals for Saving RD/WR Addresses
	bit [ADDR_SIZE-1:0] WR_addr, RD_addr;

	/*Internal signals (For Visual Clarity) defining:
	 					- signal: 1st 2-bits of din
	 					- data:   content of din*/
	signal_e signal;
	logic [ADDR_SIZE-1:0] data;

	//Outputs of Golden Model
	bit tx_valid_exp;
	bit [ADDR_SIZE-1:0] dout_exp;

	//Number of Tests
	parameter TESTS = 10000;

	//Correct Count and Error Count Signals
	int correct_count, error_count;

	//Object Creation
	RAM_class #(ADDR_SIZE) ram_c = new();


	//Clock Generation
	initial begin
   		clk = 0;
   		forever #1 clk = ~clk;
	end

	//Sampling Clock
	bit samp_clk;
	initial begin
   		samp_clk = 0;
   		forever #2 samp_clk = ~samp_clk;
	end

	//DUT Instantiation
	ram #(.MEM_DEPTH(MEM_DEPTH), .ADDR_SIZE(ADDR_SIZE)) DUT(.clk(clk), .rst_n(rst_n), .rx_valid(rx_valid), .din(din), .tx_valid(tx_valid), .dout(dout));

	//Binding Assertions
	bind DUT RAM_sva ram_sva_inst (clk, rst_n, rx_valid, din, tx_valid, dout, mem, write_addr, read_addr);


	//Sampling for Covergroup
	/*always @(posedge clk or negedge rst_n) begin
		if(~rst_n) ram_c.RAM_cg.stop();
		else ram_c.RAM_cg.sample();
	end*/

	always @(posedge samp_clk) ram_c.RAM_cg.sample();

	initial begin

		//Assert Reset - Initial State
		assert_reset;




		/*TEST 0: 	- Checks (rst_n) Functionality
					- RAM outputs (dout, tx_valid) reset to zero @(rst_n = 0)
					- Randomization Under No Constraints*/
		stimulus_gen_reset;



		//Deassert Reset
		deassert_reset;




		/*Writing data 	- Filling up RAM with initial values
						- rx_valid = 1
						- 1st 2-bits of din (signal) = 2'b00: Save WR Address
						- THEN:              signal  = 2'b01: WRITE Operation*/
		ram_initial;




		/*TEST 1:	- Checks Normal Operation of RAM
					- RAM should use din 					if(rx_valid = 1)
					- Saves WR address 						if(signal = 2'b00)
					- Writes data in pre-given address 		if(signal = 2'b01)
					- Saves RD address 						if(signal = 2'b10)
					- Reads data from pre-given address 	if(signal = 2'b11)
		*/
		stimulus_gen1;


		//TEST 2: Complete Randomization
		stimulus_gen2;



		//Correct Count and Error Count Display
		$display("At End of Simulation: Correct Count = %0d, Error Count = %0d", correct_count, error_count);
		@(negedge clk); $stop;

	end





	//Tasks

	//Assert Reset
	task assert_reset;
		rst_n = 0;
		ram_c.c.constraint_mode(0);

		@(negedge clk);
	endtask

	//TEST 0: Reset Asserted
	task stimulus_gen_reset;
		for(int i=0; i<TESTS; i++) begin
			assert(ram_c.randomize());
			rx_valid 	= ram_c.rx_valid;
			din 		= {two_bit'(ram_c.signal), ram_c.data};

			signal			= ram_c.signal;
			data 			= ram_c.data;

			check_reset;
		end
	endtask

	//CHECKER: Reset Asserted
	task check_reset;
		@(negedge clk);

		if(dout !== 0) begin
			$display("ERROR: (Reset Asserted) -> Output -dout- equals %0h, but should equal 0 \t\t--time: %0t", dout, $time);
			error_count++;
		end
		else correct_count++;

		if(tx_valid !== 0) begin
			$display("ERROR: (Reset Asserted) -> Output -tx_valid- equals %0h, but should equal 0 \t\t--time: %0t", tx_valid, $time);
			error_count++;
		end
		else correct_count++;

		@(negedge clk);
	endtask

	//Deassert Reset
	task deassert_reset;
		rst_n = 1;
		din[ADDR_SIZE+1 : ADDR_SIZE] = WRITE_DATA;		//Setting a starting point after reset is deasserted
		ram_c.c.constraint_mode(1);

		@(negedge clk);
	endtask






	//RAM data initialization
	task ram_initial;
		for(int i=0; i<TESTS; i++) begin
			rx_valid = 1;

			//Data randomized to only include write-related signals
			assert(ram_c.randomize() with {signal inside {STORE_WR_ADDR, WRITE_DATA};});
			rst_n 	= ram_c.rst_n;
			din 	= {two_bit'(ram_c.signal), ram_c.data};

			signal		= ram_c.signal;
			data 		= ram_c.data;

			//To access RAM_assoc
			golden_model;
			@(negedge clk);
		end
	endtask




	//TEST 1: Normal Operation
	task stimulus_gen1;
		for(int i=0; i<TESTS; i++) begin
			assert(ram_c.randomize());
			rst_n 		= ram_c.rst_n;
			rx_valid	= ram_c.rx_valid;
			din 		= {two_bit'(ram_c.signal), ram_c.data};

			signal			= ram_c.signal;
			data 			= ram_c.data;

			check_result;
		end
	endtask


	//TEST 2: Complete Randomization
	task stimulus_gen2;
		ram_c.c.constraint_mode(0);

		rst_n = 1;
		for(int i=0; i<TESTS; i++) begin
			assert(ram_c.randomize());
			rx_valid	= ram_c.rx_valid;
			din 		= {two_bit'(ram_c.signal), ram_c.data};

			signal			= ram_c.signal;
			data 			= ram_c.data;

			check_result;
		end
	endtask






	//CHECKER: General
	task check_result;
		@(posedge clk);

		golden_model;

		if(!rst_n) check_reset;
		else begin
			@(negedge clk);

			if(dout !== dout_exp) begin
				$display("ERROR: Output -dout- equals %0h, but should equal %0h \t\t--time: %0t", dout, dout_exp, $time);
				error_count++;
			end
			else correct_count++;

			if(tx_valid !== tx_valid_exp) begin
				$display("ERROR: Output -tx_valid- equals %0h, but should equal %0h \t\t--time: %0t", tx_valid, tx_valid_exp, $time);
				error_count++;
			end
			else correct_count++;
		end

		//To prepare available addresses for read operations -> passed to class
		ram_c.WR_addr = WR_addr;
		@(negedge clk);
	endtask

	//Golden Model
	task golden_model;
		if(!rst_n) begin
			tx_valid_exp = 0;
			dout_exp = 0;
			WR_addr = 0;
			RD_addr = 0;
		end
		else begin
			if(rx_valid) begin
				case(signal)
				STORE_WR_ADDR:	WR_addr = data;

				WRITE_DATA: 	RAM_assoc[WR_addr] = data;

				STORE_RD_ADDR: 	RD_addr = data;

				READ_DATA: 		dout_exp = RAM_assoc[RD_addr];
				endcase

				if(signal == READ_DATA) tx_valid_exp = 1;
				else tx_valid_exp = 0;
			end
		end
	endtask

endmodule