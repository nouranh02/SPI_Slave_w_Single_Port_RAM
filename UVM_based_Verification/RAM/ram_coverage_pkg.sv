package ram_coverage_pkg;
import uvm_pkg::*;
import shared_pkg::*;
import ram_sequence_item_pkg::*;

`include "uvm_macros.svh"

	class ram_coverage extends uvm_component;
		`uvm_component_utils(ram_coverage);

		uvm_analysis_export #(ram_sequence_item) cov_export;
		uvm_tlm_analysis_fifo #(ram_sequence_item) cov_fifo;

		ram_sequence_item cov_seq_item;

		covergroup cg;
			signal_cp:		coverpoint cov_seq_item.signal iff (cov_seq_item.rx_valid){
				bins WR_states[] 	= {STORE_WR_ADDR, WRITE_DATA};
				bins RD_states[] 	= {STORE_RD_ADDR, READ_DATA_};
				bins WR_to_RD		= (STORE_WR_ADDR => WRITE_DATA => STORE_RD_ADDR, READ_DATA_);	//Normal Operation: Read after Write
				bins RD_to_WR		= (STORE_RD_ADDR => READ_DATA_ => STORE_WR_ADDR, WRITE_DATA);	//Proposed Scenario: Write after Read
			}

			data_cp: 		coverpoint cov_seq_item.data iff (cov_seq_item.rx_valid){				//Ensuring access to all bits of data and memory
				bins ALL_ones 		= {ALL_ONES};
				bins ZERO 			= {ZERO};
				bins Walking_ones 	= {2**(ADDR_SIZE-1), 2**(ADDR_SIZE-2), 2**(ADDR_SIZE-3), 2**(ADDR_SIZE-4), 2**(ADDR_SIZE-5), 2**(ADDR_SIZE-6), 2**(ADDR_SIZE-7), 2**(ADDR_SIZE-8)};
				bins others			= default;
			}

			cross_signal_data: 		cross signal_cp, data_cp{
				bins WR_data 		= binsof(signal_cp.WR_states) && binsof(data_cp);			//All corners of data came along Write States
				bins RD_data 		= binsof(signal_cp.RD_states) && binsof(data_cp);			//All corners of data came along Read States
				bins data_WR_trans	= binsof(signal_cp.WR_to_RD) && binsof(data_cp);			//All corners of data came along the transition from Write States to Read States
				bins data_RW_trans	= binsof(signal_cp.RD_to_WR) && binsof(data_cp);			//All corners of data came along the transition from Read States to Write States
			}
		endgroup

		function new(string name = "ram_coverage", uvm_component parent = null);
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

	endclass : ram_coverage
	
endpackage : ram_coverage_pkg