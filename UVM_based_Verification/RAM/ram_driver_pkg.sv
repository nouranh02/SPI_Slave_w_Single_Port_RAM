package ram_driver_pkg;
import ram_sequence_item_pkg::*;
import shared_pkg::*;
import uvm_pkg::*;
`include "uvm_macros.svh"
	
	class ram_driver extends uvm_driver #(ram_sequence_item);
		`uvm_component_utils(ram_driver)

		virtual ram_if ram_drv_vif;
		virtual ram_ref_if ram_ref_drv_vif;
		ram_sequence_item stim_seq_item;

		function new(string name = "ram_driver", uvm_component parent = null);
			super.new(name, parent);
		endfunction : new

		task run_phase(uvm_phase phase);
			super.run_phase(phase);
			forever begin
				stim_seq_item = ram_sequence_item::type_id::create("stim_seq_item");
				seq_item_port.get_next_item(stim_seq_item);
				//DUT
				ram_drv_vif.rst_n 						= stim_seq_item.rst_n;
				ram_drv_vif.rx_valid 					= stim_seq_item.rx_valid;
				ram_drv_vif.din[ADDR_SIZE+1:ADDR_SIZE] 	= stim_seq_item.signal;
				ram_drv_vif.din[ADDR_SIZE-1:0] 			= stim_seq_item.data;

				//REF
				ram_ref_drv_vif.rst_n 						= stim_seq_item.rst_n;
				ram_ref_drv_vif.rx_valid 					= stim_seq_item.rx_valid;
				ram_ref_drv_vif.din[ADDR_SIZE+1:ADDR_SIZE] 	= stim_seq_item.signal;
				ram_ref_drv_vif.din[ADDR_SIZE-1:0] 			= stim_seq_item.data;
				
				@(negedge ram_drv_vif.clk);
				seq_item_port.item_done();
				`uvm_info("run_phase", stim_seq_item.convert2string_stimulus(), UVM_HIGH);
			end
		endtask : run_phase
		
	endclass : ram_driver

endpackage : ram_driver_pkg