package SPI_Wrapper_coverage_pkg;
import uvm_pkg::*;
import shared_pkg::*;
import SPI_Wrapper_sequence_item_pkg::*;

`include "uvm_macros.svh"

	class SPI_Wrapper_coverage extends uvm_component;
		`uvm_component_utils(SPI_Wrapper_coverage);

		uvm_analysis_export #(SPI_Wrapper_sequence_item) cov_export;
		uvm_tlm_analysis_fifo #(SPI_Wrapper_sequence_item) cov_fifo;

		SPI_Wrapper_sequence_item cov_seq_item;

		covergroup cg;

			//All addresses are exercised 
			wr_address_cp:		coverpoint temp_txn_wr_add[ADDR_SIZE-1:0];
			rd_address_cp:		coverpoint temp_txn_rd_add[ADDR_SIZE-1:0];

			//All Combinations of data are covered 
			wr_data_cp:			coverpoint temp_txn_wr_data[ADDR_SIZE-1:0];
			rd_data_cp:			coverpoint temp_txn_rd_data[ADDR_SIZE-1:0];

			//All Combinations of Control Signals are covered
			cross_rst_SS: 		cross cov_seq_item.rst_n, cov_seq_item.SS_n, cov_seq_item.MOSI;

			//All addresses/data experienced the effect of rst_n signal
			cross_rst_wr_add: 	cross cov_seq_item.rst_n, wr_address_cp;
			cross_rst_wr_data: 	cross cov_seq_item.rst_n, wr_data_cp;
			cross_rst_rd_add: 	cross cov_seq_item.rst_n, rd_address_cp;
			cross_rst_rd_data: 	cross cov_seq_item.rst_n, rd_data_cp;

			//All addresses/data experienced the effect of SS_n signal
			cross_SS_wr_add: 	cross cov_seq_item.SS_n, wr_address_cp;
			cross_SS_wr_data: 	cross cov_seq_item.SS_n, wr_data_cp;
			cross_SS_rd_add: 	cross cov_seq_item.SS_n, rd_address_cp;
			cross_SS_rd_data: 	cross cov_seq_item.SS_n, rd_data_cp;

		endgroup

		function new(string name = "SPI_Wrapper_coverage", uvm_component parent = null);
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

	endclass : SPI_Wrapper_coverage
	
endpackage : SPI_Wrapper_coverage_pkg