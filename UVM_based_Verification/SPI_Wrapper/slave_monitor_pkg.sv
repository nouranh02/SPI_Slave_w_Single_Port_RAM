package slave_monitor_pkg;
import uvm_pkg::*;
import shared_pkg::*;
import slave_sequence_item_pkg::*;

`include "uvm_macros.svh"

	class slave_monitor extends uvm_monitor;
		`uvm_component_utils(slave_monitor)

		slave_sequence_item rsp_seq_item;
		virtual slave_if slave_mon_vif;
		virtual slave_ref_if slave_ref_mon_vif;
		uvm_analysis_port #(slave_sequence_item) mon_ap;

		function new(string name = "slave_monitor", uvm_component parent = null);
			super.new(name, parent);
		endfunction : new

		function void build_phase(uvm_phase phase);
			super.build_phase(phase);
			mon_ap = new("mon_ap", this);
		endfunction : build_phase

		task run_phase(uvm_phase phase);
			super.run_phase(phase);

			forever begin
				rsp_seq_item = slave_sequence_item::type_id::create("rsp_seq_item");
				@(negedge slave_mon_vif.clk);
				rsp_seq_item.rst_n 			= slave_mon_vif.rst_n;
				rsp_seq_item.SS_n 			= slave_mon_vif.SS_n;
				rsp_seq_item.MOSI 			= slave_mon_vif.MOSI;
				rsp_seq_item.tx_valid 		= slave_mon_vif.tx_valid;
				rsp_seq_item.tx_data 		= slave_mon_vif.tx_data;
				rsp_seq_item.MISO 			= slave_mon_vif.MISO;
				rsp_seq_item.rx_valid 		= slave_mon_vif.rx_valid;
				rsp_seq_item.rx_data 		= slave_mon_vif.rx_data;
				rsp_seq_item.MISO_ref 		= slave_ref_mon_vif.MISO_ref;
				rsp_seq_item.rx_valid_ref 	= slave_ref_mon_vif.rx_valid_ref;
				rsp_seq_item.rx_data_ref 	= slave_ref_mon_vif.rx_data_ref;

				mon_ap.write(rsp_seq_item);
				`uvm_info("run_phase", rsp_seq_item.convert2string(), UVM_HIGH);
			end
		endtask : run_phase
		
	endclass : slave_monitor
	
endpackage : slave_monitor_pkg