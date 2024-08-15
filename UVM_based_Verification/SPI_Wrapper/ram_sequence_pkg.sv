package ram_sequence_pkg;
import uvm_pkg::*;
import ram_sequence_item_pkg::*;
import shared_pkg::*;
`include "uvm_macros.svh"

parameter TESTS = 20000;

	class ram_reset_sequence extends uvm_sequence #(ram_sequence_item);
		`uvm_object_utils(ram_reset_sequence)

		ram_sequence_item seq_item;

		function new(string name = "ram_reset_sequence");
			super.new(name);
		endfunction : new

		task body();
			seq_item = ram_sequence_item::type_id::create("seq_item");
			seq_item.constraint_mode(0);
			repeat(TESTS/10) begin
				start_item(seq_item);
				assert(seq_item.randomize() with {rst_n == 0;});
				finish_item(seq_item);
			end
		endtask : body

	endclass : ram_reset_sequence



	class ram_write_only_sequence extends uvm_sequence #(ram_sequence_item);
		`uvm_object_utils(ram_write_only_sequence)

		ram_sequence_item seq_item;

		function new(string name = "ram_write_only_sequence");
			super.new(name);
		endfunction : new

		task body();
			seq_item = ram_sequence_item::type_id::create("seq_item");
			seq_item.constraint_mode(1);
			seq_item.read_op_c.constraint_mode(0);
			repeat(TESTS) begin
				start_item(seq_item);
				assert(seq_item.randomize() with {signal inside {STORE_WR_ADDR, WRITE_DATA};  rx_valid == 1;});
				finish_item(seq_item);
			end
		endtask : body

	endclass : ram_write_only_sequence



	class ram_read_only_sequence extends uvm_sequence #(ram_sequence_item);
		`uvm_object_utils(ram_read_only_sequence)

		ram_sequence_item seq_item;

		function new(string name = "ram_read_only_sequence");
			super.new(name);
		endfunction : new

		task body();
			seq_item = ram_sequence_item::type_id::create("seq_item");
			seq_item.constraint_mode(1);
			seq_item.write_op_c.constraint_mode(0);
			repeat(TESTS) begin
				start_item(seq_item);
				assert(seq_item.randomize() with {signal inside {STORE_RD_ADDR, READ_DATA_};  rx_valid == 1;});
				finish_item(seq_item);
			end
		endtask : body

	endclass : ram_read_only_sequence



	class ram_write_read_sequence extends uvm_sequence #(ram_sequence_item);
		`uvm_object_utils(ram_write_read_sequence)

		ram_sequence_item seq_item;

		function new(string name = "ram_write_read_sequence");
			super.new(name);
		endfunction : new

		task body();
			seq_item = ram_sequence_item::type_id::create("seq_item");
			seq_item.constraint_mode(1);
			repeat(TESTS) begin
				start_item(seq_item);
				assert(seq_item.randomize());
				finish_item(seq_item);
			end
		endtask : body

	endclass : ram_write_read_sequence



	class main_sequence extends uvm_sequence #(ram_sequence_item);
		`uvm_object_utils(main_sequence)

		ram_sequence_item seq_item;

		function new(string name = "main_sequence");
			super.new(name);
		endfunction : new

		task body();
			seq_item = ram_sequence_item::type_id::create("seq_item");
			seq_item.constraint_mode(0);
			seq_item.c.constraint_mode(1);
			repeat(TESTS) begin
				start_item(seq_item);
				assert(seq_item.randomize());
				finish_item(seq_item);
			end
		endtask : body

	endclass : main_sequence

endpackage : ram_sequence_pkg