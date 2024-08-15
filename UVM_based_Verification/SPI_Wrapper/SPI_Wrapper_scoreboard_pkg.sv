package SPI_Wrapper_scoreboard_pkg;
import uvm_pkg::*;
import shared_pkg::*;
import SPI_Wrapper_sequence_item_pkg::*;

`include "uvm_macros.svh"

	class SPI_Wrapper_scoreboard extends uvm_scoreboard;
		`uvm_component_utils(SPI_Wrapper_scoreboard);

		SPI_Wrapper_sequence_item sb_seq_item;
		uvm_analysis_export #(SPI_Wrapper_sequence_item) sb_export;
		uvm_tlm_analysis_fifo #(SPI_Wrapper_sequence_item) sb_fifo;

		int correct_count, error_count;


		function new(string name = "SPI_Wrapper_scoreboard", uvm_component parent = null);
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
				
				if(sb_seq_item.MISO !== sb_seq_item.MISO_ref) begin
					`uvm_error("run_phase", $sformatf("Comparison Failed, Transaction received by DUT: %s, while the reference output -MISO-:0b%0b", sb_seq_item.convert2string(), sb_seq_item.MISO_ref));
					error_count++;
				end
				else begin
					`uvm_info("run_phase", $sformatf("Correct SPI_Wrapper output -MISO-: %s", sb_seq_item.convert2string()), UVM_HIGH);
					correct_count++;
				end
			end
				
		endtask : run_phase

		function void report_phase(uvm_phase phase);
			super.report_phase(phase);
			`uvm_info("report_phase", $sformatf("Total Successful Transactions: %0d", correct_count), UVM_MEDIUM);
			`uvm_info("report_phase", $sformatf("Total Failed Transactions: %0d", error_count), UVM_MEDIUM);
		endfunction : report_phase

	endclass : SPI_Wrapper_scoreboard

endpackage : SPI_Wrapper_scoreboard_pkg