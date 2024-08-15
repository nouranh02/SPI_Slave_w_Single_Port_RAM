package slave_driver_pkg;
import slave_sequence_item_pkg::*;
import shared_pkg::*;
import uvm_pkg::*;
`include "uvm_macros.svh"
	
	class slave_driver extends uvm_driver #(slave_sequence_item);
		`uvm_component_utils(slave_driver)

		virtual slave_if slave_drv_vif;
		virtual slave_ref_if slave_ref_drv_vif;

		slave_sequence_item stim_seq_item;

		function new(string name = "slave_driver", uvm_component parent = null);
			super.new(name, parent);
		endfunction : new

		task run_phase(uvm_phase phase);
			super.run_phase(phase);
			forever begin
				stim_seq_item = slave_sequence_item::type_id::create("stim_seq_item");
				seq_item_port.get_next_item(stim_seq_item);
				//DUT
				slave_drv_vif.rst_n 	= stim_seq_item.rst_n;
				slave_drv_vif.SS_n 		= stim_seq_item.SS_n;
				slave_drv_vif.MOSI		= stim_seq_item.MOSI;
				slave_drv_vif.tx_valid 	= stim_seq_item.tx_valid;
				slave_drv_vif.tx_data	= stim_seq_item.tx_data;

				//REF
				slave_ref_drv_vif.rst_n 	= stim_seq_item.rst_n;
				slave_ref_drv_vif.SS_n 		= stim_seq_item.SS_n;
				slave_ref_drv_vif.MOSI		= stim_seq_item.MOSI;
				slave_ref_drv_vif.tx_valid 	= stim_seq_item.tx_valid;
				slave_ref_drv_vif.tx_data	= stim_seq_item.tx_data;
				
				@(negedge slave_drv_vif.clk);
				seq_item_port.item_done();
				`uvm_info("run_phase", stim_seq_item.convert2string_stimulus(), UVM_HIGH);
			end
		endtask : run_phase
		
	endclass : slave_driver

endpackage : slave_driver_pkg