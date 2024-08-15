package slave_sequence_item_pkg;
import uvm_pkg::*;
import shared_pkg::*;
`include "uvm_macros.svh"

	class slave_sequence_item extends uvm_sequence_item;
		`uvm_object_utils(slave_sequence_item)

		rand bit MOSI, SS_n, rst_n, tx_valid;
		rand logic [ADDR_SIZE-1:0] tx_data;

		bit rx_valid, rx_valid_ref, MISO, MISO_ref;
		logic [ADDR_SIZE+1:0] rx_data, rx_data_ref;

		//state_e cs, ns;

		rand bit [1:0] selector_tx;

		function new(string name = "slave_sequence_item");
			super.new(name);
		endfunction : new

		function string convert2string();
			return $sformatf("%s 	rst_n = 0b%0b, 	SS_n = 0b%0b, 	MOSI = 0b%0b, 	tx_valid = 0b%0b, 	tx_data = 0x%0h, 	MISO = 0b%0b, 	rx_valid = 0b%0b, 	rx_data = 0x%0h",
								super.convert2string(), rst_n, SS_n, MOSI, tx_valid, tx_data, MISO, rx_valid, rx_data);
		endfunction : convert2string

		function string convert2string_stimulus();
			return $sformatf("rst_n = 0b%0b, 	SS_n = 0b%0b, 	MOSI = 0b%0b, 	tx_valid = 0b%0b, 	tx_data = 0x%0h",
								rst_n, SS_n, MOSI, tx_valid, tx_data);
		endfunction : convert2string_stimulus

		//Constraints
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
		

	endclass : slave_sequence_item
	
endpackage : slave_sequence_item_pkg