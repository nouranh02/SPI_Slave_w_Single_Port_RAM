import wrapper_pkg::*;


module SPI_Wrapper_tb;
	//Parameters
	parameter ADDR_SIZE = 8;
	parameter MEM_DEPTH = 256;

	//Inputs to DUT
	bit clk, rst_n, SS_n, MOSI;

	//Outputs of DUT
	logic MISO;

	//Outputs of Golden Model
	logic MISO_exp;

	//Target Address and Data in RAM (Used in Stimulus Generation)
	bit [ADDR_SIZE+1:0] temp_data;
	bit [ADDR_SIZE-1:0] temp_address;
	bit [ADDR_SIZE-1:0] saved_MISO;

	//Number of Tests
	parameter TESTS = 10000;

	//Correct Count and Error Count Signals
	int correct_count, error_count;

	//Object Creation
	wrapper_class #(.ADDR_SIZE(ADDR_SIZE), .MEM_DEPTH(MEM_DEPTH)) wrap = new();


	//Clock Generation
	initial begin
   		forever begin
   			#1 clk = ~clk;
   			wrap.clk = clk;
   		end
	end


	//DUT Instantiation
	SPI_Wrapper #(.ADDR_SIZE(ADDR_SIZE), .MEM_DEPTH(MEM_DEPTH)) DUT (.clk(clk), .rst_n(rst_n), .SS_n(SS_n), .MOSI(MOSI), .MISO(MISO));

	//Golden Model Instantiation
	MASTER_SPI_gm #(.ADDR_SIZE(ADDR_SIZE), .MEM_DEPTH(MEM_DEPTH)) GM (.clk(clk), .rst_n(rst_n), .SS_n(SS_n), .MOSI(MOSI), .MISO(MISO_exp));

	//Binding Assertions
	bind DUT wrapper_sva #(.ADDR_SIZE(ADDR_SIZE), .MEM_DEPTH(MEM_DEPTH)) wrap_sva_inst (MOSI,MISO,SS_n,clk,rst_n,DUT.r1.mem,DUT.s1.cs,DUT.tx_valid1,DUT.tx_data1,DUT.rx_valid1,DUT.rx_data1);



	initial begin

		//Assert Reset - Initial State
		assert_reset;




		/*TEST 0: 	- Checks (rst_n) Functionality
					- Output (MISO) resets to zero @(rst_n = 0)
					- Randomization Under No Constraints
		*/
		stimulus_gen_reset;




		//Deassert Reset
		deassert_reset;





		/*TEST 1:	- Write Data to a specific address
					- All Addresses are Exercised
					- Read from the Same address
					- Semi Directed Test Cases
		*/
		stimulus_gen1;





		/*TEST 2:	- Normal Operation of SPI
					- Randomization of MOSI bit (rst_n inactive, SS_n deactivates each 30 clock cycles)
					- SS_n is deacitvated not directly after the supposed ending of a state -> Checking for IDLE behavior
					- MISO should always equal zero unless MOSI's first 3 bits, following SS_n falling edge, equal 3'b111
		*/
		stimulus_gen2;




		/*TEST 3:	- Randomization under Constraints ((rst_n inactive, SS_n active) most of the time)
					- MOSI bits (representing data/address) experience the effect of rst_n and SS_n
					- Ensuring Control Signal's access to all RAM's addresses
					- MISO should always equal zero unless MOSI's first 3 bits, following SS_n falling edge, equal 3'b111
		*/
		stimulus_gen3;





		/*TEST 4:	- Randomization under Constraints ((rst_n inactive, SS_n active) most of the time)
					- rst_n active -> Output resets to zero
					- SS_n inactive -> Output resets to zero
					- Otherwise, MOSI bits control the flow
					- MISO should always equal zero unless MOSI's first 3 bits, following SS_n falling edge, equal 3'b111
		*/
		stimulus_gen4;







		//Correct Count and Error Count Display
		$display("At End of Simulation: Correct Count = %0d, Error Count = %0d", correct_count, error_count);
		@(negedge clk); $stop;

	end





	///////////////////////////////////////////////////////////////////// 		Tasks 		/////////////////////////////////////////////////////////////////////



	//////////////////////////////Reset-Related//////////////////////////////

	//Assert Reset
	task assert_reset;
		rst_n = 0;
		wrap.constraint_mode(0);

		@(negedge clk);
	endtask

	//TEST 0: Reset Asserted
	task stimulus_gen_reset;
		for(int i=0; i<TESTS; i++) begin
			assert(wrap.randomize());
			SS_n 		= wrap.SS_n;
			MOSI 		= wrap.MOSI;

			check_reset;
			@(negedge clk);
		end
	endtask

	//CHECKER: Reset Asserted
	task check_reset;
		@(posedge clk);

		if(MISO !== 0) begin
			$display("ERROR: (Reset Asserted) -> Output -MISO- equals %0h, but should equal 0 \t\t--time: %0t", MISO, $time);
			error_count++;
		end
		else correct_count++;
	endtask

	//Deassert Reset
	task deassert_reset;
		rst_n = 1;
		SS_n = 1;						//Setting a Starting Point following rst_n deassertion
		wrap.constraint_mode(1);

		@(negedge clk);
	endtask






	//////////////////////////////Stimulus Generation//////////////////////////////


	//Marks the beginning of every possible sequence
	task start_seq;
		SS_n = 0;
		@(negedge clk);
	endtask

	//TEST 1: Same Address (Write then Read)
	task stimulus_gen1;
		for(int i=0; i<TESTS; i++) begin
			assert(wrap.randomize());
			temp_address = wrap.temp_address;

			//Send Write Address
			start_seq;

			MOSI = 0;
			repeat (3) @(negedge clk);

			for(int i=0; i<ADDR_SIZE; i++) begin
				MOSI = temp_address[ADDR_SIZE-1-i];
				@(negedge clk);
			end

			SS_n = 1;
			@(negedge clk);
			
			//Send Write Data
			start_seq;

			MOSI = 0;
			repeat (2) @(negedge clk);
			MOSI = 1;
			@(negedge clk);

			for(int i=0; i<ADDR_SIZE; i++) begin
				assert(wrap.randomize());
				MOSI = wrap.MOSI;
				saved_MISO[ADDR_SIZE-1-i] = wrap.MOSI;
				@(negedge clk);
			end

			SS_n = 1;
			@(negedge clk);

			//Send Read Address (= Write Address)
			start_seq;

			MOSI = 1;
			repeat (2) @(negedge clk);
			MOSI = 0;
			@(negedge clk);

			for(int i=0; i<ADDR_SIZE; i++) begin
				MOSI = temp_address[ADDR_SIZE-1-i];
				@(negedge clk);
			end

			SS_n = 1;
			@(negedge clk);

			//Wait for Read Data
			start_seq;

			MOSI = 1;
			repeat (3) @(negedge clk);

			for(int i=0; i<ADDR_SIZE; i++) begin
				assert(wrap.randomize());
				MOSI = wrap.MOSI;
				@(negedge clk);
			end

			repeat (2) @(negedge clk);

			for(int i=0; i<ADDR_SIZE; i++) begin
				check_rd_after_wr(i);
				@(negedge clk);
			end

			SS_n = 1;
			@(negedge clk);
		end

	endtask



	//TEST 2: Normal Operation
	task stimulus_gen2;
		for(int i=0; i<TESTS; i++) begin
			SS_n = 0;
			for(int i=0; i<30; i++) begin
				assert(wrap.randomize());
				MOSI = wrap.MOSI;
				@(negedge clk);
			end
			SS_n = 1;
			@(negedge clk);
		end
	endtask



	//TEST 3: SS_n and rst_n randomized accross all data/addresses (MISO bits)
	task stimulus_gen3;
		wrap.constraint_mode(1);
		for(int i=0; i<TESTS; i++) begin
			assert(wrap.randomize());
			temp_data	= wrap.temp_data;
			for(int i=0; i<ADDR_SIZE+2; i++) begin
				assert(wrap.randomize());
				rst_n 	= wrap.rst_n;
				SS_n 	= wrap.SS_n;
				MOSI 	= temp_data[i];
				@(negedge clk);
			end
		end
	endtask



	//TEST 3: Randomization 
	task stimulus_gen4;
		wrap.constraint_mode(1);
		for(int i=0; i<TESTS; i++) begin
			assert(wrap.randomize());
			rst_n 	= wrap.rst_n;
			SS_n  	= wrap.SS_n;
			MOSI  	= wrap.MOSI;

			@(negedge clk);
		end
	endtask


	







	//////////////////////////////Checking Results//////////////////////////////

	//CHECKER:

	//General Checking
	always @(negedge clk or negedge rst_n) begin
		if(~rst_n) check_reset;
		else check_result;
	end

	task check_result;
		if(MISO !== MISO_exp) begin
			$display("ERROR: Output -MISO- equals %0h, but should equal %0h \t\t--time: %0t", MISO, MISO_exp, $time);
			error_count++;
		end
		else correct_count++;
	endtask


	//Specific to Consecutive Write and Read Operations
	task check_rd_after_wr(int i);
		if(MISO !== saved_MISO[ADDR_SIZE-1-i]) begin
			$display("ERROR (Corrupted RAM Data): Output -MISO- equals %0h, but should equal %0h \t\t--time: %0t", MISO, saved_MISO[ADDR_SIZE-1-i], $time);
			error_count++;
		end
		else correct_count++;
	endtask





	//////////////////////////////Functional Coverage Related//////////////////////////////


	//Sampling of Covergroup
	always @(posedge clk) wrap.wrapper_cg.sample();


endmodule