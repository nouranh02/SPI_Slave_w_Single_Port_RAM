package ram_scoreboard_pkg;
import uvm_pkg::*;
import shared_pkg::*;
import ram_sequence_item_pkg::*;

`include "uvm_macros.svh"

	class ram_scoreboard extends uvm_scoreboard;
		`uvm_component_utils(ram_scoreboard);

		ram_sequence_item sb_seq_item;
		uvm_analysis_export #(ram_sequence_item) sb_export;
		uvm_tlm_analysis_fifo #(ram_sequence_item) sb_fifo;

		int correct_count_dout, error_count_dout;
		int correct_count_tx, error_count_tx;


		function new(string name = "ram_scoreboard", uvm_component parent = null);
			super.new(name, parent);
		endfunction : new

		function void build_phase(uvm_phase phase);
			super.build_phase(phase);
			sb_export = new("sb_export", this);
			sb_fifo = new("sb_fifo", this);
		endfunction : build_phase

		function void connect_phase(uvm_phase phase);
			super.connect_phase(phase);
			sb_export.connect(sb_fifo.analysis_export);
		endfunction : connect_phase

		task run_phase(uvm_phase phase);
			super.run_phase(phase);
			forever begin
				sb_fifo.get(sb_seq_item);
				
				if(sb_seq_item.dout !== sb_seq_item.dout_ref) begin
					`uvm_error("run_phase", $sformatf("Comparison Failed, Transaction received by DUT: %s, while the reference output -dout-:0b%0b", sb_seq_item.convert2string(), sb_seq_item.dout_ref));
					error_count_dout++;
				end
				else begin
					`uvm_info("run_phase", $sformatf("Correct RAM output -dout-: %s", sb_seq_item.convert2string()), UVM_HIGH);
					correct_count_dout++;
				end

				if(sb_seq_item.tx_valid !== sb_seq_item.tx_valid_ref) begin
					`uvm_error("run_phase", $sformatf("Comparison Failed, Transaction received by DUT: %s, while the reference output -tx_valid-:0b%0b", sb_seq_item.convert2string(), sb_seq_item.tx_valid_ref));
					error_count_tx++;
				end
				else begin
					`uvm_info("run_phase", $sformatf("Correct RAM output -tx_valid-: %s", sb_seq_item.convert2string()), UVM_HIGH);
					correct_count_tx++;
				end
			end
				
		endtask : run_phase

		function void report_phase(uvm_phase phase);
			super.report_phase(phase);
			`uvm_info("report_phase", $sformatf("Total Successful Transactions -dout-: %0d", correct_count_dout), UVM_MEDIUM);
			`uvm_info("report_phase", $sformatf("Total Failed Transactions -dout-: %0d", error_count_dout), UVM_MEDIUM);
			`uvm_info("report_phase", $sformatf("Total Successful Transactions -tx_valid-: %0d", correct_count_tx), UVM_MEDIUM);
			`uvm_info("report_phase", $sformatf("Total Failed Transactions -tx_valid-: %0d", error_count_tx), UVM_MEDIUM);
		endfunction : report_phase

	endclass : ram_scoreboard

endpackage : ram_scoreboard_pkg