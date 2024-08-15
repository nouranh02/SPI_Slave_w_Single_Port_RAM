package slave_sequence_pkg;
import uvm_pkg::*;
import slave_sequence_item_pkg::*;
import shared_pkg::*;
`include "uvm_macros.svh"

parameter TESTS = 3000;
/*
	class default_sequences extends uvm_sequence #(slave_sequence_item);

		////////////////////////////////START & END////////////////////////////////
		task start_seq(slave_sequence_item seq_item);
			seq_item = slave_sequence_item::type_id::create("seq_item");
			start_item(seq_item);
			assert(seq_item.randomize() with {rst_n == 1; SS_n == 0;})
			finish_item(seq_item);
		endtask : start_seq

		task end_seq(slave_sequence_item seq_item);
			seq_item = slave_sequence_item::type_id::create("seq_item");
			start_item(seq_item);
			assert(seq_item.randomize() with {rst_n == 1; SS_n == 1;});
			finish_item(seq_item);
		endtask : end_seq

		//////////////////////////////WRITE_ADDRESS//////////////////////////////
		task write_add_seq(slave_sequence_item seq_item);
			start_seq(seq_item);
			repeat(3) begin
				seq_item = slave_sequence_item::type_id::create("seq_item");
				start_item(seq_item);
				assert(seq_item.randomize() with {rst_n == 1; SS_n == 0; MOSI == 0;})
				finish_item(seq_item);
			end

			repeat(ADDR_SIZE) begin
				seq_item = slave_sequence_item::type_id::create("seq_item");
				start_item(seq_item);
				assert(seq_item.randomize() with {rst_n == 1; SS_n == 0;});
				finish_item(seq_item);
			end
			end_seq(seq_item);
		endtask : write_add_seq

		///////////////////////////////WRITE_DATA///////////////////////////////
		task write_data_seq(slave_sequence_item seq_item);
			start_seq(seq_item);
			repeat(2) begin
				seq_item = slave_sequence_item::type_id::create("seq_item");
				start_item(seq_item);
				assert(seq_item.randomize() with {rst_n == 1; SS_n == 0; MOSI == 0;})
				finish_item(seq_item);
			end

			seq_item = slave_sequence_item::type_id::create("seq_item");
			start_item(seq_item);
			assert(seq_item.randomize() with {rst_n == 1; SS_n == 0; MOSI == 1;})
			finish_item(seq_item);

			repeat(ADDR_SIZE) begin
				seq_item = slave_sequence_item::type_id::create("seq_item");
				start_item(seq_item);
				assert(seq_item.randomize() with {rst_n == 1; SS_n == 0;});
				finish_item(seq_item);
			end
			end_seq(seq_item);
		endtask : write_data_seq

		//////////////////////////////READ_ADDRESS//////////////////////////////
		task read_add_seq(slave_sequence_item seq_item);
			start_seq(seq_item);
			repeat(2) begin
				seq_item = slave_sequence_item::type_id::create("seq_item");
				start_item(seq_item);
				assert(seq_item.randomize() with {rst_n == 1; SS_n == 0; MOSI == 1;})
				finish_item(seq_item);
			end

			seq_item = slave_sequence_item::type_id::create("seq_item");
			start_item(seq_item);
			assert(seq_item.randomize() with {rst_n == 1; SS_n == 0; MOSI == 0;})
			finish_item(seq_item);

			repeat(ADDR_SIZE) begin
				seq_item = slave_sequence_item::type_id::create("seq_item");
				start_item(seq_item);
				assert(seq_item.randomize() with {rst_n == 1; SS_n == 0;});
				finish_item(seq_item);
			end
			end_seq(seq_item);
		endtask : read_add_seq

		///////////////////////////////READ_DATA///////////////////////////////
		task read_data_seq(slave_sequence_item seq_item);
			start_seq(seq_item);
			repeat(3) begin
				seq_item = slave_sequence_item::type_id::create("seq_item");
				start_item(seq_item);
				assert(seq_item.randomize() with {rst_n == 1; SS_n == 0; MOSI == 1;})
				finish_item(seq_item);
			end

			repeat(ADDR_SIZE) begin
				seq_item = slave_sequence_item::type_id::create("seq_item");
				start_item(seq_item);
				assert(seq_item.randomize() with {rst_n == 1; SS_n == 0;});
				finish_item(seq_item);
			end
			end_seq(seq_item);
		endtask : read_data_seq

	endclass : default_sequences
*/
	class slave_reset_sequence extends uvm_sequence #(slave_sequence_item);
		`uvm_object_utils(slave_reset_sequence)

		slave_sequence_item seq_item;

		function new(string name = "slave_reset_sequence");
			super.new(name);
		endfunction : new

		task body();
			repeat(TESTS/10) begin
				seq_item = slave_sequence_item::type_id::create("seq_item");
				start_item(seq_item);
				seq_item.constraint_mode(0);
				assert(seq_item.randomize() with {rst_n == 0;});
				finish_item(seq_item);
			end
		endtask : body

	endclass : slave_reset_sequence



	class slave_write_only_sequence extends uvm_sequence #(slave_sequence_item);
		`uvm_object_utils(slave_write_only_sequence)

		slave_sequence_item seq_item;

		function new(string name = "slave_write_only_sequence");
			super.new(name);
		endfunction : new

		task body();
			repeat(TESTS) begin
				write_add_seq(seq_item);
				write_data_seq(seq_item);
			end
		endtask : body

		////////////////////////////////START & END////////////////////////////////
		task start_seq(slave_sequence_item seq_item);
			seq_item = slave_sequence_item::type_id::create("seq_item");
			start_item(seq_item);
			assert(seq_item.randomize() with {rst_n == 1; SS_n == 0;})
			finish_item(seq_item);
		endtask : start_seq

		task end_seq(slave_sequence_item seq_item);
			seq_item = slave_sequence_item::type_id::create("seq_item");
			start_item(seq_item);
			assert(seq_item.randomize() with {rst_n == 1; SS_n == 1;});
			finish_item(seq_item);
		endtask : end_seq

		//////////////////////////////WRITE_ADDRESS//////////////////////////////
		task write_add_seq(slave_sequence_item seq_item);
			start_seq(seq_item);
			repeat(3) begin
				seq_item = slave_sequence_item::type_id::create("seq_item");
				start_item(seq_item);
				assert(seq_item.randomize() with {rst_n == 1; SS_n == 0; MOSI == 0;})
				finish_item(seq_item);
			end

			repeat(ADDR_SIZE) begin
				seq_item = slave_sequence_item::type_id::create("seq_item");
				start_item(seq_item);
				assert(seq_item.randomize() with {rst_n == 1; SS_n == 0;});
				finish_item(seq_item);
			end
			end_seq(seq_item);
		endtask : write_add_seq

		///////////////////////////////WRITE_DATA///////////////////////////////
		task write_data_seq(slave_sequence_item seq_item);
			start_seq(seq_item);
			repeat(2) begin
				seq_item = slave_sequence_item::type_id::create("seq_item");
				start_item(seq_item);
				assert(seq_item.randomize() with {rst_n == 1; SS_n == 0; MOSI == 0;})
				finish_item(seq_item);
			end

			seq_item = slave_sequence_item::type_id::create("seq_item");
			start_item(seq_item);
			assert(seq_item.randomize() with {rst_n == 1; SS_n == 0; MOSI == 1;})
			finish_item(seq_item);

			repeat(ADDR_SIZE) begin
				seq_item = slave_sequence_item::type_id::create("seq_item");
				start_item(seq_item);
				assert(seq_item.randomize() with {rst_n == 1; SS_n == 0;});
				finish_item(seq_item);
			end
			end_seq(seq_item);
		endtask : write_data_seq

	endclass : slave_write_only_sequence



	class slave_read_only_sequence extends uvm_sequence #(slave_sequence_item);
		`uvm_object_utils(slave_read_only_sequence)

		slave_sequence_item seq_item;

		function new(string name = "slave_read_only_sequence");
			super.new(name);
		endfunction : new

		task body();
			repeat(TESTS) begin
				read_add_seq(seq_item);
				read_data_seq(seq_item);
			end
		endtask : body

		////////////////////////////////START & END////////////////////////////////
		task start_seq(slave_sequence_item seq_item);
			seq_item = slave_sequence_item::type_id::create("seq_item");
			start_item(seq_item);
			assert(seq_item.randomize() with {rst_n == 1; SS_n == 0;})
			finish_item(seq_item);
		endtask : start_seq

		task end_seq(slave_sequence_item seq_item);
			seq_item = slave_sequence_item::type_id::create("seq_item");
			start_item(seq_item);
			assert(seq_item.randomize() with {rst_n == 1; SS_n == 1;});
			finish_item(seq_item);
		endtask : end_seq

		//////////////////////////////READ_ADDRESS//////////////////////////////
		task read_add_seq(slave_sequence_item seq_item);
			start_seq(seq_item);
			repeat(2) begin
				seq_item = slave_sequence_item::type_id::create("seq_item");
				start_item(seq_item);
				assert(seq_item.randomize() with {rst_n == 1; SS_n == 0; MOSI == 1;})
				finish_item(seq_item);
			end

			seq_item = slave_sequence_item::type_id::create("seq_item");
			start_item(seq_item);
			assert(seq_item.randomize() with {rst_n == 1; SS_n == 0; MOSI == 0;})
			finish_item(seq_item);

			repeat(ADDR_SIZE) begin
				seq_item = slave_sequence_item::type_id::create("seq_item");
				start_item(seq_item);
				assert(seq_item.randomize() with {rst_n == 1; SS_n == 0;});
				finish_item(seq_item);
			end
			end_seq(seq_item);
		endtask : read_add_seq

		///////////////////////////////READ_DATA///////////////////////////////
		task read_data_seq(slave_sequence_item seq_item);
			start_seq(seq_item);
			repeat(3) begin
				seq_item = slave_sequence_item::type_id::create("seq_item");
				start_item(seq_item);
				assert(seq_item.randomize() with {rst_n == 1; SS_n == 0; MOSI == 1;})
				finish_item(seq_item);
			end

			repeat(ADDR_SIZE) begin
				seq_item = slave_sequence_item::type_id::create("seq_item");
				start_item(seq_item);
				assert(seq_item.randomize() with {rst_n == 1; SS_n == 0;});
				finish_item(seq_item);
			end

			repeat(ADDR_SIZE+2) begin
				seq_item = slave_sequence_item::type_id::create("seq_item");
				start_item(seq_item);
				assert(seq_item.randomize() with {rst_n == 1; SS_n == 0;});
				finish_item(seq_item);
			end
			end_seq(seq_item);
		endtask : read_data_seq

	endclass : slave_read_only_sequence



	class slave_write_read_sequence extends uvm_sequence #(slave_sequence_item);
		`uvm_object_utils(slave_write_read_sequence)

		slave_sequence_item seq_item;

		function new(string name = "slave_write_read_sequence");
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
		task start_seq(slave_sequence_item seq_item);
			seq_item = slave_sequence_item::type_id::create("seq_item");
			start_item(seq_item);
			assert(seq_item.randomize() with {rst_n == 1; SS_n == 0;})
			finish_item(seq_item);
		endtask : start_seq

		task end_seq(slave_sequence_item seq_item);
			seq_item = slave_sequence_item::type_id::create("seq_item");
			start_item(seq_item);
			assert(seq_item.randomize() with {rst_n == 1; SS_n == 1;});
			finish_item(seq_item);
		endtask : end_seq

		//////////////////////////////WRITE_ADDRESS//////////////////////////////
		task write_add_seq(slave_sequence_item seq_item);
			start_seq(seq_item);
			repeat(3) begin
				seq_item = slave_sequence_item::type_id::create("seq_item");
				start_item(seq_item);
				assert(seq_item.randomize() with {rst_n == 1; SS_n == 0; MOSI == 0;})
				finish_item(seq_item);
			end

			repeat(ADDR_SIZE) begin
				seq_item = slave_sequence_item::type_id::create("seq_item");
				start_item(seq_item);
				assert(seq_item.randomize() with {rst_n == 1; SS_n == 0;});
				finish_item(seq_item);
			end
			end_seq(seq_item);
		endtask : write_add_seq

		///////////////////////////////WRITE_DATA///////////////////////////////
		task write_data_seq(slave_sequence_item seq_item);
			start_seq(seq_item);
			repeat(2) begin
				seq_item = slave_sequence_item::type_id::create("seq_item");
				start_item(seq_item);
				assert(seq_item.randomize() with {rst_n == 1; SS_n == 0; MOSI == 0;})
				finish_item(seq_item);
			end

			seq_item = slave_sequence_item::type_id::create("seq_item");
			start_item(seq_item);
			assert(seq_item.randomize() with {rst_n == 1; SS_n == 0; MOSI == 1;})
			finish_item(seq_item);

			repeat(ADDR_SIZE) begin
				seq_item = slave_sequence_item::type_id::create("seq_item");
				start_item(seq_item);
				assert(seq_item.randomize() with {rst_n == 1; SS_n == 0;});
				finish_item(seq_item);
			end
			end_seq(seq_item);
		endtask : write_data_seq

		//////////////////////////////READ_ADDRESS//////////////////////////////
		task read_add_seq(slave_sequence_item seq_item);
			start_seq(seq_item);
			repeat(2) begin
				seq_item = slave_sequence_item::type_id::create("seq_item");
				start_item(seq_item);
				assert(seq_item.randomize() with {rst_n == 1; SS_n == 0; MOSI == 1;})
				finish_item(seq_item);
			end

			seq_item = slave_sequence_item::type_id::create("seq_item");
			start_item(seq_item);
			assert(seq_item.randomize() with {rst_n == 1; SS_n == 0; MOSI == 0;})
			finish_item(seq_item);

			repeat(ADDR_SIZE) begin
				seq_item = slave_sequence_item::type_id::create("seq_item");
				start_item(seq_item);
				assert(seq_item.randomize() with {rst_n == 1; SS_n == 0;});
				finish_item(seq_item);
			end
			end_seq(seq_item);
		endtask : read_add_seq

		///////////////////////////////READ_DATA///////////////////////////////
		task read_data_seq(slave_sequence_item seq_item);
			start_seq(seq_item);
			repeat(3) begin
				seq_item = slave_sequence_item::type_id::create("seq_item");
				start_item(seq_item);
				assert(seq_item.randomize() with {rst_n == 1; SS_n == 0; MOSI == 1;})
				finish_item(seq_item);
			end

			repeat(ADDR_SIZE) begin
				seq_item = slave_sequence_item::type_id::create("seq_item");
				start_item(seq_item);
				assert(seq_item.randomize() with {rst_n == 1; SS_n == 0;});
				finish_item(seq_item);
			end

			repeat(ADDR_SIZE+2) begin
				seq_item = slave_sequence_item::type_id::create("seq_item");
				start_item(seq_item);
				assert(seq_item.randomize() with {rst_n == 1; SS_n == 0;});
				finish_item(seq_item);
			end
			end_seq(seq_item);
		endtask : read_data_seq

	endclass : slave_write_read_sequence
	


	class slave_main_sequence extends uvm_sequence #(slave_sequence_item);
		`uvm_object_utils(slave_main_sequence)

		slave_sequence_item seq_item;

		function new(string name = "slave_main_sequence");
			super.new(name);
		endfunction : new

		task body();
			repeat(TESTS) begin
				seq_item = slave_sequence_item::type_id::create("seq_item");
				start_item(seq_item);
				assert(seq_item.randomize());
				finish_item(seq_item);
			end
		endtask : body

	endclass : slave_main_sequence

endpackage : slave_sequence_pkg