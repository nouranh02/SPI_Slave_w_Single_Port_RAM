package SPI_Wrapper_monitor_pkg;
import uvm_pkg::*;
import shared_pkg::*;
import SPI_Wrapper_sequence_item_pkg::*;

`include "uvm_macros.svh"

	class SPI_Wrapper_monitor extends uvm_monitor;
		`uvm_component_utils(SPI_Wrapper_monitor)

		SPI_Wrapper_sequence_item rsp_seq_item;
		virtual SPI_Wrapper_if SPI_Wrapper_mon_vif;
		virtual SPI_Wrapper_ref_if SPI_Wrapper_ref_mon_vif;
		uvm_analysis_port #(SPI_Wrapper_sequence_item) mon_ap;

		function new(string name = "SPI_Wrapper_monitor", uvm_component parent = null);
			super.new(name, parent);
		endfunction : new

		function void build_phase(uvm_phase phase);
			super.build_phase(phase);
			mon_ap = new("mon_ap", this);
		endfunction : build_phase

		task run_phase(uvm_phase phase);
			super.run_phase(phase);

			forever begin
				rsp_seq_item = SPI_Wrapper_sequence_item::type_id::create("rsp_seq_item");
				@(negedge SPI_Wrapper_mon_vif.clk);
				rsp_seq_item.rst_n 			= SPI_Wrapper_mon_vif.rst_n;
				rsp_seq_item.SS_n 			= SPI_Wrapper_mon_vif.SS_n;
				rsp_seq_item.MOSI 			= SPI_Wrapper_mon_vif.MOSI;
				rsp_seq_item.MISO 			= SPI_Wrapper_mon_vif.MISO;
				rsp_seq_item.MISO_ref		= SPI_Wrapper_ref_mon_vif.MISO_ref;

				mon_ap.write(rsp_seq_item);
				`uvm_info("run_phase", rsp_seq_item.convert2string(), UVM_HIGH);
			end
		endtask : run_phase
		
	endclass : SPI_Wrapper_monitor
	
endpackage : SPI_Wrapper_monitor_pkg