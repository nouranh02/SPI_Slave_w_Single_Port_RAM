package RAM_pkg;

	typedef enum logic [1:0] {STORE_WR_ADDR, WRITE_DATA, STORE_RD_ADDR, READ_DATA} signal_e;
	typedef bit [1:0] two_bit;
	
	class RAM_class #(int ADDR_SIZE = 8);

		bit clk;
		rand bit rst_n, rx_valid;
		rand logic [ADDR_SIZE-1:0] data;
		rand signal_e signal;

		//For post randomization
		logic [ADDR_SIZE-1:0] data_old;
		signal_e signal_old;

		//For specifying valid addresses (that have been written previously)
		logic [ADDR_SIZE-1:0] valid_addr_q[$];
		bit [ADDR_SIZE-1:0] WR_addr;


		//Parameters for data Constraints
		parameter ONES = (2**ADDR_SIZE) - 1;
		parameter ZERO = 0;

		rand bit [1:0] selector_data;

		constraint c {
			rst_n 			dist {0:=5, 	1:=95};							//rst_n is inactive most of the time
			rx_valid 		dist {0:=30, 	1:=70};							//rx_valid is active most of the time

			(signal_old == STORE_WR_ADDR) -> signal == WRITE_DATA;		//Whenever a "SAVE WR ADDRESS" signal is sent, it's followed by a "WRITE DATA" signal

			(signal_old == STORE_RD_ADDR) -> signal == READ_DATA;		//Whenever a "SAVE RD ADDRESS" signal is sent, it's followed by a "READ DATA" signal

			selector_data  	dist {[0:1]:/40, 2:=40, 3:=20};				//Data is at its corner cases most of the time

			if(selector_data == 0) 			data == {ONES};
			else if(selector_data == 1) 	data == {ZERO};
			else if(selector_data == 2)		$countones(data) == 1;
		}

		constraint valid_addr {
			(signal == STORE_RD_ADDR) -> data inside {valid_addr_q};	//"SAVE RD ADDRESS" has to be followed by an address that is readable
		}

		function void post_randomize;
			data_old 	= data;
			signal_old 	= signal;

			if(rst_n && rx_valid && (signal == WRITE_DATA)) valid_addr_q.push_front(WR_addr);	//Whenever a successful WRITE OP is done in a specific address,
		endfunction																				//that address is pushed to the valid_addr queue

		covergroup RAM_cg;
			signal_cp:		coverpoint signal{
				bins WR_states 	= {STORE_WR_ADDR, WRITE_DATA};
				bins RD_states 	= {STORE_RD_ADDR, READ_DATA};
				bins WR_to_RD	= (STORE_WR_ADDR => WRITE_DATA => STORE_RD_ADDR, READ_DATA);	//Normal Operation: Read after Write
				bins RD_to_WR	= (STORE_RD_ADDR => READ_DATA => STORE_WR_ADDR, WRITE_DATA);	//Proposed Scenario: Write after Read
			}

			data_cp: 		coverpoint data{					//Ensuring access to all bits of data and memory
				bins ALL_ones 		= {ONES};
				bins ZERO 			= {0};
				bins Walking_ones 	= {2**(ADDR_SIZE-1), 2**(ADDR_SIZE-2), 2**(ADDR_SIZE-3), 2**(ADDR_SIZE-4), 2**(ADDR_SIZE-5), 2**(ADDR_SIZE-6), 2**(ADDR_SIZE-7), 2**(ADDR_SIZE-8)};
			}
			rx_valid_cp: 	coverpoint rx_valid;
			WR_addr_cp: 	coverpoint WR_addr;													//All RAM addresses have been covered 

			cross_rst_addr: 		cross rst_n, WR_addr_cp; 									//All RAM addresses heve experienced the effect of rst_n
			cross_rx_addr: 			cross rx_valid_cp, WR_addr_cp; 								//All RAM addresses heve experienced the effect of rx_valid

			cross_rst_signal: 		cross rst_n, signal_cp; 									//All States and Transitions heve experienced the effect of rst_n

			cross_signal_data: 		cross signal_cp, data_cp{
				bins WR_data 		= binsof(signal_cp.WR_states) && binsof(data_cp);			//All corners of data came along Write States
				bins RD_data 		= binsof(signal_cp.RD_states) && binsof(data_cp);			//All corners of data came along Read States
				bins data_WR_trans	= binsof(signal_cp.WR_to_RD) && binsof(data_cp);			//All corners of data came along the transition from Write States to Read States
				bins data_RW_trans	= binsof(signal_cp.RD_to_WR) && binsof(data_cp);			//All corners of data came along the transition from Read States to Write States
			}

			cross_signal_rx: 		cross signal_cp, rx_valid_cp{
				bins WR_valid 		= binsof(signal_cp.WR_states) && binsof(rx_valid_cp) intersect {1};		//WR states are entered at active rx_valid
				bins RD_valid 		= binsof(signal_cp.RD_states) && binsof(rx_valid_cp) intersect {1};		//RD states are entered at active rx_valid
				bins WR_to_RD_valid = binsof(signal_cp.WR_to_RD) && binsof(rx_valid_cp) intersect {1};		//Transition from WR to RD states is done at active rx_valid
				bins RD_to_WR_valid = binsof(signal_cp.RD_to_WR) && binsof(rx_valid_cp) intersect {1};		//Transition from RD to WR states is done at active rx_valid
				bins states_IDLE	= binsof(signal_cp) && binsof(rx_valid_cp) intersect {0};				//All states and transitions passed IDLE state (inactive rx_valid)
			}

			cross_signal_addr: 		cross signal_cp, WR_addr_cp{
				bins WR_OP	 		= binsof(signal_cp.WR_states) && binsof(WR_addr_cp);		//The same addresses passed accross both Write States
				bins RD_OP 			= binsof(signal_cp.RD_states) && binsof(WR_addr_cp);		//The same addresses passed accross both Read States
				bins WR_to_RD_addr  = binsof(signal_cp.WR_to_RD) && binsof(WR_addr_cp);			//The same addresses passed accross WR to RD Transition
				bins RD_to_WR_addr  = binsof(signal_cp.RD_to_WR) && binsof(WR_addr_cp);			//The same addresses passed accross WR to RD Transition
			}
		endgroup

		function new(bit reset = 0, valid = 0, logic [ADDR_SIZE-1:0] content = 0, signal_e sig = STORE_WR_ADDR);
			this.rst_n 		= reset;
			this.rx_valid	= valid;
			this.data 		= content;
			this.signal 	= sig;

			RAM_cg = new();
		endfunction

	endclass

endpackage