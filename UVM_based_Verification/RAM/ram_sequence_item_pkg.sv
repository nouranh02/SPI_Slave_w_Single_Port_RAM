package ram_sequence_item_pkg;
import uvm_pkg::*;
import shared_pkg::*;
`include "uvm_macros.svh"

	class ram_sequence_item extends uvm_sequence_item;
		`uvm_object_utils(ram_sequence_item)

		rand bit rst_n, rx_valid;
		//rand logic [ADDR_SIZE+1:0] din;
		logic [ADDR_SIZE-1:0] dout;
		bit tx_valid;

		logic [ADDR_SIZE-1:0] dout_ref;
		bit tx_valid_ref;

		rand signal_e signal;
		rand logic [ADDR_SIZE-1:0] data;

		//For post randomization
		signal_e signal_old;

		//For specifying valid addresses (that have been written previously)
		logic [ADDR_SIZE-1:0] valid_addr_q[$];

		rand bit [1:0] selector_data;

		function new(string name = "ram_sequence_item");
			super.new(name);
		endfunction : new

		function string convert2string();
			return $sformatf("%s 	rst_n = 0b%0b, 	rx_valid = 0b%0b, 	din = 0x%0h, 	tx_valid = 0b%0b, 	dout = 0x%0h",
								super.convert2string(), rst_n, rx_valid, {signal, data}, tx_valid, dout);
		endfunction : convert2string

		function string convert2string_stimulus();
			return $sformatf("rst_n = 0b%0b, 	rx_valid = 0b%0b, 	din = 0x%0h",
								rst_n, rx_valid, {signal, data});
		endfunction : convert2string_stimulus

		//Constraints
		constraint c {
			rst_n 			dist {0:=5, 	1:=95};							//rst_n is inactive most of the time
			rx_valid 		dist {0:=30, 	1:=70};							//rx_valid is active most of the time

			selector_data  	dist {[0:2]:/30, 3:=70};						//Data is at its corner cases for some time

			if(selector_data == 0) 			data == {ALL_ONES};
			else if(selector_data == 1) 	data == {ZERO};
			else if(selector_data == 2)		$countones(data) == 1;

			//(signal == STORE_RD_ADDR)		-> data inside {valid_addr_q};
		}
		
		constraint write_op_c {
			(signal_old == STORE_WR_ADDR) 	-> signal == WRITE_DATA;		//Whenever a "SAVE WR ADDRESS" signal is sent, it's followed by a "WRITE DATA" signal
		}
		
		constraint read_op_c {
			(signal_old == STORE_RD_ADDR) 	-> signal == READ_DATA_;		//Whenever a "SAVE RD ADDRESS" signal is sent, it's followed by a "READ DATA" signal
		}

		function void post_randomize;
			//if(rst_n && rx_valid && (signal == STORE_WR_ADDR)) valid_addr_q.push_front(data);
			signal_old 	= signal;
		endfunction
		

	endclass : ram_sequence_item
	
endpackage : ram_sequence_item_pkg