import slave_pkg::*;


module slave_tb;
	//Parameters
	parameter ADDR_SIZE = 8;

	//Inputs to DUT
	bit MOSI, SS_n, clk, rst_n, tx_valid;
	logic [ADDR_SIZE-1:0] tx_data;

	//Outputs of DUT
	bit MISO, rx_valid;
	logic [ADDR_SIZE+1:0] rx_data;

	//Outputs of Golden Model
	bit MISO_exp, rx_valid_exp;
	logic [ADDR_SIZE+1:0] rx_data_exp;

	//Number of Tests
	parameter TESTS = 10000;

	//Correct Count and Error Count Signals
	int correct_count, error_count;

	//Object Creation
	slave_class #(ADDR_SIZE) sc = new();

	//For Visual Clarity
	//cs and ns of DUT
	state_dut_e cs_DUT, ns_DUT;
	assign cs_DUT = state_dut_e'(DUT.cs);
	assign ns_DUT = state_dut_e'(DUT.ns);

	//cs and ns of GM
	state_gm_e cs_gm, ns_gm;
	assign cs_gm = state_gm_e'(GM.cs);
	assign ns_gm = state_gm_e'(GM.ns);



	//Clock Generation
	initial begin
   		forever begin
   			#1 clk = ~clk;
   			sc.clk = clk;
   		end
	end


	//DUT Instantiation
	slave #(.ADDR_SIZE(ADDR_SIZE)) DUT (.clk(clk), .rst_n(rst_n), .MOSI(MOSI), .SS_n(SS_n) , .tx_valid(tx_valid), .tx_data(tx_data), .rx_data(rx_data), .rx_valid(rx_valid), .MISO(MISO));

	//Golden Model Instantiation
	SPI_SLAVE #(.ADDR_SIZE(ADDR_SIZE)) GM (.clk(clk), .rst_n(rst_n), .MOSI(MOSI), .SS_n(SS_n) , .tx_valid(tx_valid), .tx_data(tx_data), .rx_data(rx_data_exp), .rx_valid(rx_valid_exp), .MISO(MISO_exp));

	//Binding Assertions
	bind DUT slave_sva slave_sva_inst (.clk(clk), .rst_n(rst_n), .MOSI(MOSI), .SS_n(SS_n) , .tx_valid(tx_valid), .tx_data(tx_data), .rx_data(rx_data), .rx_valid(rx_valid), .MISO(MISO), .cs(cs), .ns(ns));



	initial begin

		//Assert Reset - Initial State
		assert_reset;




		/*TEST 0: 	- Checks (rst_n) Functionality
					- slave outputs (rx_data, rx_valid, MISO) reset to zero @(rst_n = 0)
					- Randomization (of all variables) is done Under No Constraints
		*/
		stimulus_gen_reset;




		//Deassert Reset
		deassert_reset;








		/*TEST 1:	- Checks Normal Write Operation of Slave
					- SS_n should equal 0 throughout the cycle -> 1 after data is collected
					- Cycle(1): MOSI should equal 0 (WRITE) -> 00 (Send Address)
					- rx_data should be ready and rx_valid should be high after 8 cycles
					- Cycle(2): MOSI should equal 0 (WRITE) -> 01 (Send Data)
					- rx_data should be ready and rx_valid should be high after 8 cycles
					- Randomization (of MOSI) is done Under No Constraints
		*/
		stimulus_gen1;


		


		/*TEST 2:	- Checks Normal Read Operation of Slave
					- SS_n should equal 0 throughout the 1st cycle -> 1 after data is collected
					- Cycle(1): MOSI should equal 1 (READ) -> 10 (Send Address)
					- Cycle(2): MOSI should equal 1 (READ) -> 11 (Receive Data)
					- MISO should translate tx_data to serial output when tx_valid is high
					- Randomization (of MOSI) is done Under No Constraints
		*/
		stimulus_gen2;





		/*TEST 3:	- Checks slave's behavior going from one sequence to another
					- Same functionality as Normal Operation
					- The slave can't go through two consecutive (READ_ADD) sequences or (READ_DATA) sequences
					- Randomization (of MOSI) is done Under No Constraints
		*/
		stimulus_gen3;





		/*TEST 4:	- Randomization of all variables under constraints:
						- rst_n is inactive most of the time
						- SS_n is active most of the time
						- tx_valid is inactive most of the time
						- tx_valid is high if cs = READ_DATA and rx_valid was high the previous cycle (to mimic RAM behavior)
					- SS_n deactivated mid-transmission -> slave goes IDLE, outputs reset to zero
					- SS_n deactivated after-transmission -> slave should stay stable
		*/
		stimulus_gen4;




		/*TEST 5:	- Randomization of all variables under constraints
					- Output is checked against golden model
		*/
		stimulus_gen5;
		



		//Correct Count and Error Count Display
		$display("At End of Simulation: Correct Count = %0d, Error Count = %0d", correct_count, error_count);
		@(negedge clk); $stop;

	end





	///////////////////////////////////////////////////////////////////// 		Tasks 		/////////////////////////////////////////////////////////////////////



	//////////////////////////////Reset-Related//////////////////////////////

	//Assert Reset
	task assert_reset;
		rst_n = 0;
		sc.constraint_mode(0);

		@(negedge clk);
	endtask

	//TEST 0: Reset Asserted
	task stimulus_gen_reset;
		for(int i=0; i<TESTS; i++) begin
			assert(sc.randomize());
			SS_n 		= sc.SS_n;
			MOSI 		= sc.MOSI;
			tx_valid 	= sc.tx_valid;
			tx_data		= sc.tx_data;

			check_reset;
			@(negedge clk);
		end
	endtask

	//CHECKER: Reset Asserted
	task check_reset;
		@(posedge clk);

		if(rx_data !== 0) begin
			$display("ERROR: (Reset Asserted) -> Output -rx_data- equals %0h, but should equal 0 \t\t--time: %0t", rx_data, $time);
			error_count++;
		end
		else correct_count++;

		if(rx_valid !== 0) begin
			$display("ERROR: (Reset Asserted) -> Output -rx_valid- equals %0h, but should equal 0 \t\t--time: %0t", rx_valid, $time);
			error_count++;
		end
		else correct_count++;

		if(MISO !== 0) begin
			$display("ERROR: (Reset Asserted) -> Output -MISO- equals %0h, but should equal 0 \t\t--time: %0t", MISO, $time);
			error_count++;
		end
		else correct_count++;
	endtask

	//Deassert Reset
	task deassert_reset;
		rst_n = 1;
		SS_n = 1;
		sc.constraint_mode(1);

		@(negedge clk);
	endtask







	///////////////////////Preparing Possible Sequences for Slave (IDLE to IDLE)///////////////////////


	/*
	To simulate RAM's behavior 	- Inputs are driven @(posedge clk)
								- tx_valid and tx_data do not change until rx_valid is high
	*/
	int rx_high_since = 0;
	always @(posedge clk) begin
		assert(sc.randomize());
		if(cs_DUT == READ_DATA) begin
			rx_high_since++;
			if(rx_high_since > ADDR_SIZE - 1) tx_valid <= 1;
			else begin
				tx_valid <= 0;
				tx_data <= sc.tx_data;
			end
		end
		else begin
			if(ns_DUT == READ_DATA) tx_valid <= 0;
			else tx_valid <= sc.tx_valid;
			rx_high_since <= 0;
			tx_data <= sc.tx_data;
		end
	end

	//Marks the beginning and ending of all sequences
	task start_seq;
		SS_n = 0;
		@(negedge clk);
	endtask

	task end_seq;
		@(negedge clk);
		SS_n = 1;
		@(negedge clk);
	endtask




	//WRITE_ADD -> MOSI: 000
	task write_add_seq;
		start_seq;
		MOSI = 0;
		repeat(2) @(negedge clk);
		for(int i=0; i<ADDR_SIZE; i++) begin
			@(negedge clk);
			assert(sc.randomize());
			MOSI = sc.MOSI;
		end
		end_seq;
	endtask

	//WRITE_DATA -> MOSI: 001
	task write_data_seq;
		start_seq;
		MOSI = 0;
		repeat(2) @(negedge clk);
		MOSI = 1;
		for(int i=0; i<ADDR_SIZE; i++) begin
			@(negedge clk);
			assert(sc.randomize());
			MOSI = sc.MOSI;
		end
		end_seq;
	endtask

	//READ_ADD -> MOSI: 110
	task read_add_seq;
		start_seq;
		MOSI = 1;
		repeat(2) @(negedge clk);
		MOSI = 0;
		for(int i=0; i<ADDR_SIZE; i++) begin
			@(negedge clk);
			assert(sc.randomize());
			MOSI = sc.MOSI;
		end
		end_seq;
	endtask

	//READ_DATA -> MOSI: 111
	task read_data_seq;
		start_seq;
		MOSI = 1;
		repeat(2) @(negedge clk);
		for(int i=0; i<ADDR_SIZE; i++) begin
			@(negedge clk);
			assert(sc.randomize());
			MOSI = sc.MOSI;
		end
		@(negedge clk);

		repeat (9) @(negedge clk);

		SS_n = 1;
		@(negedge clk);
	endtask




	//////////////////////////////Stimulus Generation//////////////////////////////


	//TEST 1: Normal Write Operation
	task stimulus_gen1;
		sc.constraint_mode(0);
		for(int i=0; i<TESTS; i++) begin
			write_add_seq;
			write_data_seq;
		end
	endtask



	//TEST 2: Normal Read Operation
	task stimulus_gen2;
		sc.constraint_mode(0);
		for(int i=0; i<TESTS; i++) begin
			read_add_seq;
			read_data_seq;
		end
	endtask



	//TEST 3: Randomization of Different Scenarios
	task stimulus_gen3;
		sc.constraint_mode(0);
		for(int i=0; i<TESTS; i++) begin
			assert(sc.randomize());
			case(sc.selector_seq)
				0: write_add_seq;
				1: write_data_seq;
				2: read_add_seq;
				3: read_data_seq;
			endcase
		end
	endtask



	//Test 4: Randomization of all variables - with Constraints
	/*task stimulus_gen4;
		sc.constraint_mode(1);
		for(int i=0; i<TESTS; i++) begin
			assert(sc.randomize());
			tx_valid = sc.tx_valid;
			tx_data	 = sc.tx_data;
			for(int i=0; i<ADDR_SIZE+2; i++) begin
				assert(sc.randomize());
				rst_n 	 = sc.rst_n;
				SS_n 	 = sc.SS_n;
				MOSI 	 = sc.MOSI;
				@(negedge clk);
			end
		end
	endtask*/


	//Test 4: Randomization of all variables - with Constraints
	task stimulus_gen4;
		sc.constraint_mode(1);
		for(int i=0; i<TESTS; i++) begin
			assert(sc.randomize());
			rst_n 	 = sc.rst_n;
			SS_n 	 = sc.SS_n;
			MOSI 	 = sc.MOSI;

			@(negedge clk);
		end
	endtask


	//Test 5: Randomization of all variables - No Constraints
	task stimulus_gen5;
		sc.constraint_mode(0);
		for(int i=0; i<TESTS; i++) begin
			assert(sc.randomize());
			rst_n 	 = sc.rst_n;
			SS_n 	 = sc.SS_n;
			MOSI 	 = sc.MOSI;

			@(negedge clk);
		end
	endtask




	//////////////////////////////Checking Results//////////////////////////////

	//CHECKER:

	always @(negedge clk or negedge rst_n) begin
		if(~rst_n) check_reset;
		else begin
			check_rx_valid;
			check_MISO;
			if(rx_valid) check_rx_data;
		end
	end

	task check_rx_valid;
		if(rx_valid !== rx_valid_exp) begin
			$display("ERROR: Output -rx_valid- equals %0h, but should equal %0h \t\t--time: %0t", rx_valid, rx_valid_exp, $time);
			error_count++;
		end
		else correct_count++;
	endtask

	task check_rx_data;
		if(rx_data !== rx_data_exp) begin
			$display("ERROR: Output -rx_data- equals %0h, but should equal %0h \t\t--time: %0t", rx_data, rx_data_exp, $time);
			error_count++;
		end
		else correct_count++;
	endtask

	task check_MISO;
		if(MISO !== MISO_exp) begin
			$display("ERROR: Output -MISO- equals %0h, but should equal %0h \t\t--time: %0t", MISO, MISO_exp, $time);
			error_count++;
		end
		else correct_count++;
	endtask






	//////////////////////////////Functional Coverage Related//////////////////////////////


	//Exporting Signals to Class -> To be included in coverpoints
	always @(negedge clk) begin
		//sc.rx_valid = rx_valid;
		sc.rx_data 	= rx_data;
		sc.cs 		= cs_DUT;
	end

	//Sampling of Covergroup
	always @(posedge clk) sc.slave_cg.sample();


endmodule