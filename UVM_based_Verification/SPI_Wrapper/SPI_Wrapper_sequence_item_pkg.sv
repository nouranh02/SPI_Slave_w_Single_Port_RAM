package SPI_Wrapper_sequence_item_pkg;
import uvm_pkg::*;
import shared_pkg::*;
`include "uvm_macros.svh"

	class SPI_Wrapper_sequence_item extends uvm_sequence_item;
		`uvm_object_utils(SPI_Wrapper_sequence_item)

		rand bit rst_n, SS_n, MOSI;

		bit MISO, MISO_ref;

		randc bit [ADDR_SIZE-1:0] txn;

		bit MOSI_txn_wr_add, MOSI_txn_wr_data, MOSI_txn_rd_add, MOSI_txn_rd_data;
		int i;

		function new(string name = "SPI_Wrapper_sequence_item");
			super.new(name);
		endfunction : new

		function string convert2string();
			return $sformatf("%s 	rst_n = 0b%0b, 	SS_n = 0b%0b, 	MOSI = 0b%0b, 	MISO = 0b%0b",
								super.convert2string(), rst_n, SS_n, MOSI, MISO);
		endfunction : convert2string

		function string convert2string_stimulus();
			return $sformatf("rst_n = 0b%0b, 	SS_n = 0b%0b, 	MOSI = 0b%0b",
								rst_n, SS_n, MOSI);
		endfunction : convert2string_stimulus

		function void pre_randomize();
			if(i == 0) begin
				MOSI_txn_wr_add = 0;
				MOSI_txn_wr_data = 0;
				MOSI_txn_rd_add = 1;
				MOSI_txn_rd_data = 1;
			end
		endfunction : pre_randomize

		//Constraints
		constraint rst_c {
			rst_n 			dist {0:=2, 	1:=98};				//rst_n is inactive most of the time
		}

		constraint SS_c {
			SS_n 			dist {0:=95,	1:=5};				//SS_n is active most of the time
		}

		constraint MOSI_wr_add_c {
			MOSI == MOSI_txn_wr_add;
		}

		constraint MOSI_wr_data_c {
			MOSI == MOSI_txn_wr_data;
		}

		constraint MOSI_rd_add_c {
			MOSI == MOSI_txn_rd_add;
		}

		constraint MOSI_rd_data_c {
			MOSI == MOSI_txn_rd_data;
		}
		
		function void post_randomize();
			if(i == 0) begin
				temp_txn_wr_add = {2'b00, txn};
				temp_txn_wr_data = {2'b01, txn};
				temp_txn_rd_add = {2'b10, txn};
				temp_txn_rd_data = {2'b11, txn};
			end
			else begin
				MOSI_txn_wr_add = temp_txn_wr_add[ADDR_SIZE + 1 - i];
				MOSI_txn_wr_data = temp_txn_wr_data[ADDR_SIZE + 1 - i];
				MOSI_txn_rd_add = temp_txn_rd_add[ADDR_SIZE + 1 - i];
				MOSI_txn_rd_data = temp_txn_rd_data[ADDR_SIZE + 1 - i];
			end
			if(i > ADDR_SIZE + 1) i = 0;
			else i++;
		endfunction : post_randomize

	endclass : SPI_Wrapper_sequence_item
	
endpackage : SPI_Wrapper_sequence_item_pkg