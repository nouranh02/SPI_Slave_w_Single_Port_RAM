package slave_coverage_pkg;
import uvm_pkg::*;
import shared_pkg::*;
import slave_sequence_item_pkg::*;

`include "uvm_macros.svh"

	class slave_coverage extends uvm_component;
		`uvm_component_utils(slave_coverage);

		uvm_analysis_export #(slave_sequence_item) cov_export;
		uvm_tlm_analysis_fifo #(slave_sequence_item) cov_fifo;

		slave_sequence_item cov_seq_item;

		covergroup cg;

			///////////////////////////////////////////////////////////////Coverpoints///////////////////////////////////////////////////////////////

			tx_data_cp:		coverpoint cov_seq_item.tx_data{
				bins Corners 	= {ZERO, ALL_ONES, 8'haa, 8'h55};	//Needs to be edited if a different ADDER_SIZE is used
				bins others[] 	= default;
			}

			rx_signal_cp: 	coverpoint cov_seq_item.rx_data[ADDR_SIZE+1:ADDR_SIZE] iff(cov_seq_item.rx_valid){
				bins signal_wr_addr	= {2'b00};
				bins signal_wr_data	= {2'b01};
				bins signal_rd_addr	= {2'b10};
				bins signal_rd_data	= {2'b11};
				bins signal_trans 	= (2'b00 => 2'b01 => 2'b10 => 2'b11);
			}

			rx_data_cp: 	coverpoint cov_seq_item.rx_data[ADDR_SIZE-1:0] iff(cov_seq_item.rx_valid){
				bins Corners 	= {ZERO, ALL_ONES, 8'haa, 8'h55};	//Needs to be edited if a different ADDER_SIZE is used
				bins others[] 	= default;
			}

			rst_n_cp: 		coverpoint cov_seq_item.rst_n;
			SS_n_cp: 		coverpoint cov_seq_item.SS_n;
			MOSI_cp: 		coverpoint cov_seq_item.MOSI;
			tx_valid_cp: 	coverpoint cov_seq_item.tx_valid;

			///////////////////////////////////////////////////////////////Cross Coverage///////////////////////////////////////////////////////////////

			cross_MOSI_SS_rst: 		cross rst_n_cp, SS_n_cp, MOSI_cp;										//All combinations of Control Signals occured

			cross_rx_signal_data: 	cross rx_signal_cp, rx_data_cp{											//Output has taken all the required values for expected usage
				ignore_bins trans = binsof(rx_signal_cp.signal_trans) && binsof(rx_data_cp);
			}

			cross_tx_valid_data: 	cross tx_data_cp, tx_valid_cp{											//All corners of read data came along active tx_valid
				bins tx_val_data 		= binsof(tx_data_cp) && binsof(tx_valid_cp) intersect {1};
				ignore_bins tx_inv 		= binsof(tx_data_cp) && binsof(tx_valid_cp) intersect {0};
			}
		endgroup

		function new(string name = "slave_coverage", uvm_component parent = null);
			super.new(name, parent);
			cg = new();
		endfunction : new

		function void build_phase(uvm_phase phase);
			super.build_phase(phase);
			cov_export = new("cov_export", this);
			cov_fifo = new("cov_fifo", this);
		endfunction : build_phase

		function void connect_phase(uvm_phase phase);
			super.connect_phase(phase);
			cov_export.connect(cov_fifo.analysis_export);
		endfunction : connect_phase

		task run_phase(uvm_phase phase);
			super.run_phase(phase);
			forever begin
				cov_fifo.get(cov_seq_item);
				cg.sample();
			end
		endtask : run_phase

	endclass : slave_coverage
	
endpackage : slave_coverage_pkg