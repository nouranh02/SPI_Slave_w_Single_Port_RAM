package wrapper_pkg;

	class wrapper_class #(int ADDR_SIZE = 8, MEM_DEPTH = 256);

		//Inputs to DUT
		bit clk;
		rand bit rst_n, SS_n, MOSI;

		//Target Address (Used in Stimulus Generation)
		rand bit [ADDR_SIZE-1:0] temp_address;
		rand bit [ADDR_SIZE+1:0] temp_data;


		constraint rst_c {
			rst_n 			dist {0:=2, 	1:=98};				//rst_n is inactive most of the time
		}

		constraint SS_c {
			SS_n 			dist {0:=95,	1:=5};				//SS_n is active most of the time
		}


		covergroup wrapper_cg;

			addresses_cp:		coverpoint temp_address;	//All Addresses are Exercised

			cross_rst_SS: 		cross rst_n, SS_n, MOSI;	//All Combinations of Control Signals are experienced

			cross_rst_n_data: 	cross rst_n, temp_data;		//All addresses/data experienced the effect of rst_n signal

			cross_SS_n_data: 	cross SS_n, temp_data;		//All addresses/data experienced the effect of SS_n signal

		endgroup

		function new(bit rst_n = 0, SS_n = 1, MOSI = 0);
			this.rst_n 		= rst_n;
			this.SS_n 		= SS_n;
			this.MOSI	 	= MOSI;

			wrapper_cg = new();
		endfunction

	endclass

endpackage