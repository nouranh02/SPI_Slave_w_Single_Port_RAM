package slave_pkg;

	typedef enum logic [2:0] {IDLE, READ_DATA, READ_ADD, CHK_CMD, WRITE, WAIT_WR, WAIT_RD, WAIT_RD2} state_dut_e;
	typedef enum logic [2:0] {IDLE_, CHK_CMD_, WRITE_, READ_ADD_, READ_DATA_, WAIT_WR_, WAIT_RD_, WAIT_RD2_} state_gm_e;

	
	class slave_class #(int ADDR_SIZE = 8);

		//Parameters for Constraints and Covergroup
		parameter ALL_ONES = 2*(ADDR_SIZE) - 1;
		parameter ZERO = 0;

		//Inputs to DUT
		bit clk;
		rand bit MOSI, SS_n, rst_n, tx_valid;
		rand logic [ADDR_SIZE-1:0] tx_data;

		//Signals Imported from Design
		bit rx_valid;
		logic [ADDR_SIZE+1:0] rx_data, rx_data_old;
		state_dut_e cs;
		//int rx_high_since = 0;

		//For tx_data Constraint
		rand bit [1:0] selector_tx;

		//For Randomizing Sequences
		rand bit [1:0] selector_seq;
		//rand bit [3:0] delay_SSn;

		/*function void pre_randomize();
			if( (cs == READ_DATA) && (rx_data == rx_data_old)) tx_valid = 1;
			else if(cs == READ_DATA) tx_valid = 0;

			//tx_valid = 1;
		endfunction*/

		constraint rst_c {
			rst_n 			dist {0:=5, 	1:=95};							//rst_n is inactive most of the time
		}

		constraint SS_c {
			SS_n 			dist {0:=90,	1:=10};							//SS_n is active most of the time
		}

		constraint tx {
			tx_valid 		dist {0:=70, 	1:=30};							//tx_valid is inactive most of the time
			selector_tx		dist {0:=30, 	1:=30,		[2:3]:=40};

			if(selector_tx == 0) tx_data inside {ALL_ONES, ZERO};
			if(selector_tx == 1) $countones(tx_data) == 1;
		}


		//To hold past values for pre_randomize conditions
		/*function void post_randomize();
			//rx_data_old  = rx_data;
			if(cs == READ_DATA) rx_high_since++;
			else rx_high_since = 0;
		endfunction*/


		covergroup slave_cg;

			///////////////////////////////////////////////////////////////Coverpoints///////////////////////////////////////////////////////////////

			tx_data_cp:		coverpoint tx_data{						//Rapid changes in tx_data might not be caught by MISO
				bins Corners 	= {ZERO, ALL_ONES, 8'haa, 8'h55};	//Needs to be edited if a different ADDER_SIZE is used
				bins low_high 	= (ZERO => ALL_ONES);
				bins high_low	= (ALL_ONES => ZERO);
			}

			cs_cp: 			coverpoint cs{							//All states, and transitions must be covered
				//States
				bins States[] 		= {IDLE, READ_DATA, READ_ADD, CHK_CMD, WRITE, WAIT_WR, WAIT_RD, WAIT_RD2};
				/*
				bins Ctrl_States 	= {IDLE, CHK_CMD};
				bins Write_States 	= {WRITE};
				bins Read_States 	= {READ_DATA, READ_ADD};
				bins hold_States 	= {WAIT_WR, WAIT_RD, WAIT_RD2};
				*/

				//Normal Transitions
				bins chk_to_all			= (CHK_CMD => IDLE, WAIT_WR, WAIT_RD);
				bins rd_add_data		= (READ_ADD => IDLE => CHK_CMD => WAIT_RD => WAIT_RD2 => READ_DATA);
				bins wr_add_data 		= (WRITE => IDLE => CHK_CMD => WAIT_WR => WRITE);

				//Illegal Transitions
				illegal_bins IDLE_to_other 		= (IDLE => READ_DATA, READ_ADD, WRITE, WAIT_WR, WAIT_RD, WAIT_RD2);
				illegal_bins CHK_to_other		= (CHK_CMD => WAIT_RD2, READ_DATA, READ_ADD, WRITE);
				illegal_bins WAIT_RD_to_other 	= (WAIT_RD => READ_DATA, READ_ADD, CHK_CMD, WRITE, WAIT_WR);

				//Different Scenarios
				bins rd_to_wr[] 	= (READ_ADD, READ_DATA => IDLE => CHK_CMD => WAIT_WR => WRITE);
				bins wr_to_rd[]		= (WRITE => IDLE => CHK_CMD => WAIT_RD => WAIT_RD2 => READ_ADD, READ_DATA);
				bins rd_wr_rd 		= (READ_ADD => IDLE => CHK_CMD => WAIT_WR => WRITE[*10] => IDLE => CHK_CMD => WAIT_RD => WAIT_RD2 => READ_DATA);
				bins wr_rd_wr[]		= (WRITE => IDLE => CHK_CMD => WAIT_RD => WAIT_RD2 => READ_ADD[*9] => IDLE => CHK_CMD => WAIT_WR => WRITE);
				bins wr_rd2_wr[]	= (WRITE => IDLE => CHK_CMD => WAIT_RD => WAIT_RD2 => READ_DATA[*18] => IDLE => CHK_CMD => WAIT_WR => WRITE);
			}

			rst_n_cp: 		coverpoint rst_n;
			SS_n_cp: 		coverpoint SS_n;
			MOSI_cp: 		coverpoint MOSI;
			tx_valid_cp: 	coverpoint tx_valid;
			

			///////////////////////////////////////////////////////////////Cross Coverage///////////////////////////////////////////////////////////////

			cross_tx_read: 			cross tx_data_cp, cs_cp{
				bins tx_read 			= binsof(tx_data_cp) && binsof(cs_cp.States) intersect {READ_ADD, READ_DATA};	//All corners of read data came along Read States
				ignore_bins tx_no_read1	= binsof(tx_data_cp) && !binsof(cs_cp.States);
				ignore_bins tx_no_read2 = binsof(tx_data_cp) && binsof(cs_cp.States) intersect {IDLE, CHK_CMD, WRITE, WAIT_WR, WAIT_RD, WAIT_RD2};
			}

			cross_tx_valid_data: 	cross tx_data_cp, tx_valid_cp{														//All corners of read data came along active tx_valid
				bins tx_val_data 		= binsof(tx_data_cp) && binsof(tx_valid_cp) intersect {1};
				ignore_bins tx_inv 		= binsof(tx_data_cp) && binsof(tx_valid_cp) intersect {0};
			}

			cross_MOSI_SS_rst: 			cross rst_n_cp, SS_n_cp, MOSI_cp;												//All combinations of Control Signals occured

			cross_rst_states: 		cross cs_cp, rst_n_cp{
				bins rst_all 			= binsof(cs_cp.States) && binsof(rst_n_cp);										//All states experienced rst_n effect (low/high)
				ignore_bins rst_trans	= !binsof(cs_cp.States) && binsof(rst_n_cp);
			}

			cross_SS_states: 		cross cs_cp, SS_n_cp{
				bins SS_all	 			= binsof(cs_cp.States) && binsof(SS_n_cp);										//All states experienced SS_n effect (low/high)
				ignore_bins SS_trans	= !binsof(cs_cp.States) && binsof(SS_n_cp);
			}
		endgroup

		function new(bit rst_n = 0, tx_valid = 0, SS_n = 1, MOSI = 0, logic [ADDR_SIZE-1:0] tx_data = 0);
			this.rst_n 		= rst_n;
			this.tx_valid	= tx_valid;
			this.SS_n 		= SS_n;
			this.MOSI	 	= MOSI;
			this.tx_data	= tx_data;

			slave_cg = new();
		endfunction

	endclass

endpackage