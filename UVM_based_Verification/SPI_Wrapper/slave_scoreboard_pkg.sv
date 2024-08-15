package slave_scoreboard_pkg;
import uvm_pkg::*;
import shared_pkg::*;
import slave_sequence_item_pkg::*;

`include "uvm_macros.svh"

	class slave_scoreboard extends uvm_scoreboard;
		`uvm_component_utils(slave_scoreboard);

		slave_sequence_item sb_seq_item;
		uvm_analysis_export #(slave_sequence_item) sb_export;
		uvm_tlm_analysis_fifo #(slave_sequence_item) sb_fifo;

		bit data_addr;

		int correct_count_rxdata, error_count_rxdata;
		int correct_count_rxvalid, error_count_rxvalid;
		int correct_count_MISO, error_count_MISO;


		function new(string name = "slave_scoreboard", uvm_component parent = null);
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

				//state_ref_model(sb_seq_item);

				if(sb_seq_item.rx_valid !== sb_seq_item.rx_valid_ref) begin
					`uvm_error("run_phase", $sformatf("Comparison Failed, Transaction received by DUT: %s, while the reference output -rx_valid-:0b%0b", sb_seq_item.convert2string(), sb_seq_item.rx_valid_ref));
					error_count_rxvalid++;
				end
				else begin
					`uvm_info("run_phase", $sformatf("Correct slave output -rx_valid-: %s", sb_seq_item.convert2string()), UVM_HIGH);
					correct_count_rxvalid++;
					if(sb_seq_item.rx_valid) begin
						if(sb_seq_item.rx_data !== sb_seq_item.rx_data_ref) begin
							`uvm_error("run_phase", $sformatf("Comparison Failed, Transaction received by DUT: %s, while the reference output -rx_data-:0x%0h", sb_seq_item.convert2string(), sb_seq_item.rx_data_ref));
							error_count_rxdata++;
						end
						else begin
							`uvm_info("run_phase", $sformatf("Correct slave output -rx_data-: %s", sb_seq_item.convert2string()), UVM_HIGH);
							correct_count_rxdata++;
						end
					end
				end

				if(sb_seq_item.MISO !== sb_seq_item.MISO_ref) begin
					`uvm_error("run_phase", $sformatf("Comparison Failed, Transaction received by DUT: %s, while the reference output -MISO-:0b%0b", sb_seq_item.convert2string(), sb_seq_item.MISO_ref));
					error_count_MISO++;
				end
				else begin
					`uvm_info("run_phase", $sformatf("Correct slave output -MISO-: %s", sb_seq_item.convert2string()), UVM_HIGH);
					correct_count_MISO++;
				end
			end
				
		endtask : run_phase
/*
		task state_ref_model(slave_sequence_item chk_seq_item);
			if(!chk_seq_item.rst_n) chk_seq_item.cs = IDLE;
			else chk_seq_item.cs = chk_seq_item.ns;

			case(chk_seq_item.cs)
				IDLE: chk_seq_item.ns = (chk_seq_item.SS_n) ? IDLE : CHK_CMD;
				CHK_CMD: begin
					if(chk_seq_item.SS_n) chk_seq_item.ns = IDLE;
					else begin
						if(chk_seq_item.MOSI) chk_seq_item.ns = WAIT_RD;
						else chk_seq_item.ns = WAIT_WR;
					end
				end
				WAIT_WR: chk_seq_item.ns = (chk_seq_item.SS_n) ? IDLE : (chk_seq_item.MOSI) ? IDLE : WRITE;
				WAIT_RD: begin
					if(chk_seq_item.SS_n) chk_seq_item.ns = IDLE;
					else begin
						if(~chk_seq_item.MOSI) chk_seq_item.ns = IDLE;
						else chk_seq_item.ns = WAIT_RD2;
					end
				end
				WAIT_RD2: begin
					if(chk_seq_item.SS_n) chk_seq_item.ns = IDLE;
					else begin
						if(chk_seq_item.MOSI && data_addr) chk_seq_item.ns = READ_DATA;
						else if(~chk_seq_item.MOSI && ~data_addr) chk_seq_item.ns = READ_ADD;
						else chk_seq_item.ns = IDLE;
					end
				end
				WRITE: chk_seq_item.ns = (chk_seq_item.SS_n) ? IDLE : WRITE;
				READ_ADD: chk_seq_item.ns = (chk_seq_item.SS_n) ? IDLE : READ_ADD;
				READ_DATA: chk_seq_item.ns = (chk_seq_item.SS_n) ? IDLE : READ_DATA;
				default: chk_seq_item.ns = IDLE;
			endcase // chk_seq_item.cs

			if(!chk_seq_item.rst_n) data_addr = 0;
			else if(chk_seq_item.cs == READ_DATA) data_addr = 1;
			else if(chk_seq_item.cs == READ_ADD) data_addr = 0;
		endtask : state_ref_model
*/
		function void report_phase(uvm_phase phase);
			super.report_phase(phase);
			`uvm_info("report_phase", $sformatf("Total Successful Transactions -rx_data-: %0d", correct_count_rxdata), UVM_MEDIUM);
			`uvm_info("report_phase", $sformatf("Total Failed Transactions -rx_data-: %0d", error_count_rxdata), UVM_MEDIUM);
			`uvm_info("report_phase", $sformatf("Total Successful Transactions -rx_valid-: %0d", correct_count_rxvalid), UVM_MEDIUM);
			`uvm_info("report_phase", $sformatf("Total Failed Transactions -rx_valid-: %0d", error_count_rxvalid), UVM_MEDIUM);
			`uvm_info("report_phase", $sformatf("Total Successful Transactions -MISO-: %0d", correct_count_MISO), UVM_MEDIUM);
			`uvm_info("report_phase", $sformatf("Total Failed Transactions -MISO-: %0d", error_count_MISO), UVM_MEDIUM);
		endfunction : report_phase

	endclass : slave_scoreboard

endpackage : slave_scoreboard_pkg