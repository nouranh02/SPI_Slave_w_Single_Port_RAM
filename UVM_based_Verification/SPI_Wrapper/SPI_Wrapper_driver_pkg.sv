package SPI_Wrapper_driver_pkg;
import SPI_Wrapper_sequence_item_pkg::*;
import shared_pkg::*;
import uvm_pkg::*;
`include "uvm_macros.svh"
	
	class SPI_Wrapper_driver extends uvm_driver #(SPI_Wrapper_sequence_item);
		`uvm_component_utils(SPI_Wrapper_driver)

		virtual SPI_Wrapper_if SPI_Wrapper_drv_vif;
		virtual SPI_Wrapper_ref_if SPI_Wrapper_ref_drv_vif;

		SPI_Wrapper_sequence_item stim_seq_item;

		function new(string name = "SPI_Wrapper_driver", uvm_component parent = null);
			super.new(name, parent);
		endfunction : new

		task run_phase(uvm_phase phase);
			super.run_phase(phase);
			forever begin
				stim_seq_item = SPI_Wrapper_sequence_item::type_id::create("stim_seq_item");
				seq_item_port.get_next_item(stim_seq_item);
				//DUT
				SPI_Wrapper_drv_vif.rst_n 		= stim_seq_item.rst_n;
				SPI_Wrapper_drv_vif.SS_n 		= stim_seq_item.SS_n;
				SPI_Wrapper_drv_vif.MOSI		= stim_seq_item.MOSI;

				//REF
				SPI_Wrapper_ref_drv_vif.rst_n 		= stim_seq_item.rst_n;
				SPI_Wrapper_ref_drv_vif.SS_n 		= stim_seq_item.SS_n;
				SPI_Wrapper_ref_drv_vif.MOSI		= stim_seq_item.MOSI;
				
				@(negedge SPI_Wrapper_drv_vif.clk);
				seq_item_port.item_done();
				`uvm_info("run_phase", stim_seq_item.convert2string_stimulus(), UVM_HIGH);
			end
		endtask : run_phase
		
	endclass : SPI_Wrapper_driver

endpackage : SPI_Wrapper_driver_pkg