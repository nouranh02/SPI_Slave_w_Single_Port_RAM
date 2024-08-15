package SPI_Wrapper_sequence_pkg;
import uvm_pkg::*;
import SPI_Wrapper_sequence_item_pkg::*;
import shared_pkg::*;
`include "uvm_macros.svh"

parameter TESTS = 3000;
/*
	class default_sequences extends uvm_sequence #(SPI_Wrapper_sequence_item);

		function new(string name = "default_sequences");
			super.new(name);
		endfunction : new

		SPI_Wrapper_sequence_item seq_item;

		////////////////////////////////START & END////////////////////////////////
		task start_seq;
			seq_item = SPI_Wrapper_sequence_item::type_id::create("seq_item");
			start_item(seq_item);
			assert(seq_item.randomize() with {rst_n == 1; SS_n == 0;})
			finish_item(seq_item);
		endtask : start_seq

		task end_seq;
			seq_item = SPI_Wrapper_sequence_item::type_id::create("seq_item");
			start_item(seq_item);
			assert(seq_item.randomize() with {rst_n == 1; SS_n == 1;});
			finish_item(seq_item);
		endtask : end_seq

		//////////////////////////////WRITE_ADDRESS//////////////////////////////
		task write_add_seq;
			start_seq;
			repeat(ADDR_SIZE + 3) begin
				seq_item = SPI_Wrapper_sequence_item::type_id::create("seq_item");
				start_item(seq_item);
				seq_item.constraint_mode(0);
				seq_item.MOSI_wr_add_c.constraint_mode(1);
				assert(seq_item.randomize() with {rst_n == 1; SS_n == 0;});
				finish_item(seq_item);
			end
			end_seq;
		endtask : write_add_seq

		///////////////////////////////WRITE_DATA///////////////////////////////
		task write_data_seq;
			start_seq;
			repeat(ADDR_SIZE + 3) begin
				seq_item = SPI_Wrapper_sequence_item::type_id::create("seq_item");
				start_item(seq_item);
				seq_item.constraint_mode(0);
				seq_item.MOSI_wr_data_c.constraint_mode(1);
				assert(seq_item.randomize() with {rst_n == 1; SS_n == 0;});
				finish_item(seq_item);
			end
			end_seq;
		endtask : write_data_seq

		//////////////////////////////READ_ADDRESS//////////////////////////////
		task read_add_seq;
			start_seq;
			repeat(ADDR_SIZE + 3) begin
				seq_item = SPI_Wrapper_sequence_item::type_id::create("seq_item");
				start_item(seq_item);
				seq_item.constraint_mode(0);
				seq_item.MOSI_rd_add_c.constraint_mode(1);
				assert(seq_item.randomize() with {rst_n == 1; SS_n == 0;});
				finish_item(seq_item);
			end
			end_seq;
		endtask : read_add_seq

		///////////////////////////////READ_DATA///////////////////////////////
		task read_data_seq;
			start_seq;
			repeat(ADDR_SIZE + 3) begin
				seq_item = SPI_Wrapper_sequence_item::type_id::create("seq_item");
				start_item(seq_item);
				seq_item.constraint_mode(0);
				seq_item.MOSI_rd_data_c.constraint_mode(1);
				assert(seq_item.randomize() with {rst_n == 1; SS_n == 0;});
				finish_item(seq_item);
			end
			end_seq;
		endtask : read_data_seq

	endclass : default_sequences
*/
	class SPI_Wrapper_reset_sequence extends uvm_sequence #(SPI_Wrapper_sequence_item);
		`uvm_object_utils(SPI_Wrapper_reset_sequence)

		SPI_Wrapper_sequence_item seq_item;

		function new(string name = "SPI_Wrapper_reset_sequence");
			super.new(name);
		endfunction : new

		task body();
			seq_item = SPI_Wrapper_sequence_item::type_id::create("seq_item");
			seq_item.constraint_mode(0);
			repeat(TESTS) begin
				start_item(seq_item);
				assert(seq_item.randomize() with {rst_n == 0;});
				finish_item(seq_item);
			end
		endtask : body

	endclass : SPI_Wrapper_reset_sequence



	class SPI_Wrapper_write_only_sequence extends uvm_sequence #(SPI_Wrapper_sequence_item);
		`uvm_object_utils(SPI_Wrapper_write_only_sequence)

		SPI_Wrapper_sequence_item seq_item;

		function new(string name = "SPI_Wrapper_write_only_sequence");
			super.new(name);
		endfunction : new

		task body();
			repeat(TESTS) begin
				write_add_seq(seq_item);
				write_data_seq(seq_item);
			end
		endtask : body

		////////////////////////////////START & END////////////////////////////////
		task start_seq(SPI_Wrapper_sequence_item seq_item);
			seq_item = SPI_Wrapper_sequence_item::type_id::create("seq_item");
			seq_item.constraint_mode(0);
			start_item(seq_item);
			assert(seq_item.randomize() with {rst_n == 1; SS_n == 0;})
			finish_item(seq_item);
		endtask : start_seq

		task end_seq(SPI_Wrapper_sequence_item seq_item);
			seq_item = SPI_Wrapper_sequence_item::type_id::create("seq_item");
			seq_item.constraint_mode(0);
			start_item(seq_item);
			assert(seq_item.randomize() with {rst_n == 1; SS_n == 1;});
			finish_item(seq_item);
		endtask : end_seq

		//////////////////////////////WRITE_ADDRESS//////////////////////////////
		task write_add_seq(SPI_Wrapper_sequence_item seq_item);
			start_seq(seq_item);
			seq_item = SPI_Wrapper_sequence_item::type_id::create("seq_item");
			seq_item.constraint_mode(0);
			seq_item.MOSI_wr_add_c.constraint_mode(1);
			repeat(ADDR_SIZE + 3) begin
				start_item(seq_item);
				assert(seq_item.randomize() with {rst_n == 1; SS_n == 0;});
				finish_item(seq_item);
			end
			end_seq(seq_item);
		endtask : write_add_seq

		///////////////////////////////WRITE_DATA///////////////////////////////
		task write_data_seq(SPI_Wrapper_sequence_item seq_item);
			start_seq(seq_item);
			seq_item = SPI_Wrapper_sequence_item::type_id::create("seq_item");
			seq_item.constraint_mode(0);
			seq_item.MOSI_wr_data_c.constraint_mode(1);
			repeat(ADDR_SIZE + 3) begin
				start_item(seq_item);
				assert(seq_item.randomize() with {rst_n == 1; SS_n == 0;});
				finish_item(seq_item);
			end
			end_seq(seq_item);
		endtask : write_data_seq

	endclass : SPI_Wrapper_write_only_sequence



	class SPI_Wrapper_read_only_sequence extends uvm_sequence #(SPI_Wrapper_sequence_item);
		`uvm_object_utils(SPI_Wrapper_read_only_sequence)

		SPI_Wrapper_sequence_item seq_item;

		function new(string name = "SPI_Wrapper_read_only_sequence");
			super.new(name);
		endfunction : new

		task body();
			repeat(TESTS) begin
				read_add_seq(seq_item);
				read_data_seq(seq_item);
			end
		endtask : body

		////////////////////////////////START & END////////////////////////////////
		task start_seq(SPI_Wrapper_sequence_item seq_item);
			seq_item = SPI_Wrapper_sequence_item::type_id::create("seq_item");
			seq_item.constraint_mode(0);
			start_item(seq_item);
			assert(seq_item.randomize() with {rst_n == 1; SS_n == 0;})
			finish_item(seq_item);
		endtask : start_seq

		task end_seq(SPI_Wrapper_sequence_item seq_item);
			seq_item = SPI_Wrapper_sequence_item::type_id::create("seq_item");
			seq_item.constraint_mode(0);
			start_item(seq_item);
			assert(seq_item.randomize() with {rst_n == 1; SS_n == 1;});
			finish_item(seq_item);
		endtask : end_seq

		//////////////////////////////READ_ADDRESS//////////////////////////////
		task read_add_seq(SPI_Wrapper_sequence_item seq_item);
			start_seq(seq_item);
			seq_item = SPI_Wrapper_sequence_item::type_id::create("seq_item");
			seq_item.constraint_mode(0);
			seq_item.MOSI_rd_add_c.constraint_mode(1);
			repeat(ADDR_SIZE + 3) begin
				start_item(seq_item);
				assert(seq_item.randomize() with {rst_n == 1; SS_n == 0;});
				finish_item(seq_item);
			end
			end_seq(seq_item);
		endtask : read_add_seq

		///////////////////////////////READ_DATA///////////////////////////////
		task read_data_seq(SPI_Wrapper_sequence_item seq_item);
			start_seq(seq_item);
			seq_item = SPI_Wrapper_sequence_item::type_id::create("seq_item");
			seq_item.constraint_mode(0);
			seq_item.MOSI_rd_data_c.constraint_mode(1);
			repeat(ADDR_SIZE + 3) begin
				start_item(seq_item);
				assert(seq_item.randomize() with {rst_n == 1; SS_n == 0;});
				finish_item(seq_item);
			end

			seq_item = SPI_Wrapper_sequence_item::type_id::create("seq_item");
			seq_item.constraint_mode(0);
			//seq_item.MOSI_rd_data_c.constraint_mode(1);
			repeat(ADDR_SIZE + 3) begin
				start_item(seq_item);
				assert(seq_item.randomize() with {rst_n == 1; SS_n == 0;});
				finish_item(seq_item);
			end
			end_seq(seq_item);
		endtask : read_data_seq

	endclass : SPI_Wrapper_read_only_sequence



	class SPI_Wrapper_write_read_sequence extends uvm_sequence #(SPI_Wrapper_sequence_item);
		`uvm_object_utils(SPI_Wrapper_write_read_sequence)

		SPI_Wrapper_sequence_item seq_item;

		function new(string name = "SPI_Wrapper_write_read_sequence");
			super.new(name);
		endfunction : new

		task body();
			repeat(TESTS) begin
				case($urandom_range(0,3))
					0: write_add_seq(seq_item);
					1: write_data_seq(seq_item);
					2: read_add_seq(seq_item);
					3: read_data_seq(seq_item);
				endcase //seq_item.selector_seq
			end
		endtask : body

		////////////////////////////////START & END////////////////////////////////
		task start_seq(SPI_Wrapper_sequence_item seq_item);
			seq_item = SPI_Wrapper_sequence_item::type_id::create("seq_item");
			seq_item.constraint_mode(0);
			start_item(seq_item);
			assert(seq_item.randomize() with {rst_n == 1; SS_n == 0;})
			finish_item(seq_item);
		endtask : start_seq

		task end_seq(SPI_Wrapper_sequence_item seq_item);
			seq_item = SPI_Wrapper_sequence_item::type_id::create("seq_item");
			seq_item.constraint_mode(0);
			start_item(seq_item);
			assert(seq_item.randomize() with {rst_n == 1; SS_n == 1;});
			finish_item(seq_item);
		endtask : end_seq

		//////////////////////////////WRITE_ADDRESS//////////////////////////////
		task write_add_seq(SPI_Wrapper_sequence_item seq_item);
			start_seq(seq_item);
			seq_item = SPI_Wrapper_sequence_item::type_id::create("seq_item");
			seq_item.constraint_mode(0);
			seq_item.MOSI_wr_add_c.constraint_mode(1);
			repeat(ADDR_SIZE + 3) begin
				start_item(seq_item);
				assert(seq_item.randomize() with {rst_n == 1; SS_n == 0;});
				finish_item(seq_item);
			end
			end_seq(seq_item);
		endtask : write_add_seq

		///////////////////////////////WRITE_DATA///////////////////////////////
		task write_data_seq(SPI_Wrapper_sequence_item seq_item);
			start_seq(seq_item);
			seq_item = SPI_Wrapper_sequence_item::type_id::create("seq_item");
			seq_item.constraint_mode(0);
			seq_item.MOSI_wr_data_c.constraint_mode(1);
			repeat(ADDR_SIZE + 3) begin
				start_item(seq_item);
				assert(seq_item.randomize() with {rst_n == 1; SS_n == 0;});
				finish_item(seq_item);
			end
			end_seq(seq_item);
		endtask : write_data_seq

		//////////////////////////////READ_ADDRESS//////////////////////////////
		task read_add_seq(SPI_Wrapper_sequence_item seq_item);
			start_seq(seq_item);
			seq_item = SPI_Wrapper_sequence_item::type_id::create("seq_item");
			seq_item.constraint_mode(0);
			seq_item.MOSI_rd_add_c.constraint_mode(1);
			repeat(ADDR_SIZE + 3) begin
				start_item(seq_item);
				assert(seq_item.randomize() with {rst_n == 1; SS_n == 0;});
				finish_item(seq_item);
			end
			end_seq(seq_item);
		endtask : read_add_seq

		///////////////////////////////READ_DATA///////////////////////////////
		task read_data_seq(SPI_Wrapper_sequence_item seq_item);
			start_seq(seq_item);
			seq_item = SPI_Wrapper_sequence_item::type_id::create("seq_item");
			seq_item.constraint_mode(0);
			seq_item.MOSI_rd_data_c.constraint_mode(1);
			repeat(ADDR_SIZE + 3) begin
				start_item(seq_item);
				assert(seq_item.randomize() with {rst_n == 1; SS_n == 0;});
				finish_item(seq_item);
			end

			seq_item = SPI_Wrapper_sequence_item::type_id::create("seq_item");
			seq_item.constraint_mode(0);
			//seq_item.MOSI_rd_data_c.constraint_mode(1);
			repeat(ADDR_SIZE + 3) begin
				start_item(seq_item);
				assert(seq_item.randomize() with {rst_n == 1; SS_n == 0;});
				finish_item(seq_item);
			end
			end_seq(seq_item);
		endtask : read_data_seq

	endclass : SPI_Wrapper_write_read_sequence
	


	class SPI_Wrapper_main_sequence extends uvm_sequence #(SPI_Wrapper_sequence_item);
		`uvm_object_utils(SPI_Wrapper_main_sequence)

		SPI_Wrapper_sequence_item seq_item;

		function new(string name = "SPI_Wrapper_main_sequence");
			super.new(name);
		endfunction : new

		task body();
			seq_item = SPI_Wrapper_sequence_item::type_id::create("seq_item");
			seq_item.constraint_mode(0);
			seq_item.rst_c.constraint_mode(1);
			seq_item.SS_c.constraint_mode(1);
			repeat(TESTS) begin
				start_item(seq_item);
				assert(seq_item.randomize());
				finish_item(seq_item);
			end
		endtask : body

	endclass : SPI_Wrapper_main_sequence

endpackage : SPI_Wrapper_sequence_pkg