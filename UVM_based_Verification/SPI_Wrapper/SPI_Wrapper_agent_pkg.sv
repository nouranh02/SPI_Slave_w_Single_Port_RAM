package SPI_Wrapper_agent_pkg;
import uvm_pkg::*;
import SPI_Wrapper_driver_pkg::*;
import SPI_Wrapper_sequencer_pkg::*;
import SPI_Wrapper_monitor_pkg::*;
import SPI_Wrapper_config_pkg::*;
import SPI_Wrapper_sequence_item_pkg::*;

`include "uvm_macros.svh"

	class SPI_Wrapper_agent extends uvm_agent;
		`uvm_component_utils(SPI_Wrapper_agent)

		SPI_Wrapper_driver drv;
		SPI_Wrapper_sequencer sqr;
		SPI_Wrapper_monitor mon;
		SPI_Wrapper_config SPI_Wrapper_cfg;
		uvm_analysis_port #(SPI_Wrapper_sequence_item) agt_ap;

		function new(string name = "SPI_Wrapper_agent", uvm_component parent = null);
			super.new(name, parent);			
		endfunction : new

		function void build_phase(uvm_phase phase);
			super.build_phase(phase);
			SPI_Wrapper_cfg = SPI_Wrapper_config::type_id::create("SPI_Wrapper_cfg", this);
			if(!uvm_config_db#(SPI_Wrapper_config)::get(this, "", "SPI_Wrapper_CFG", SPI_Wrapper_cfg))
				`uvm_fatal("build_phase", "Agent - Unable to get SPI_Wrapper Configuration Object.");

			if(SPI_Wrapper_cfg.active) begin
				drv = SPI_Wrapper_driver::type_id::create("drv", this);
				sqr = SPI_Wrapper_sequencer::type_id::create("sqr", this);
			end
			mon = SPI_Wrapper_monitor::type_id::create("mon", this);

			agt_ap = new("agt_ap", this);
		endfunction : build_phase

		function void connect_phase(uvm_phase phase);
			super.connect_phase(phase);
			if(SPI_Wrapper_cfg.active) begin
				drv.SPI_Wrapper_drv_vif = SPI_Wrapper_cfg.SPI_Wrapper_vif;
				drv.SPI_Wrapper_ref_drv_vif = SPI_Wrapper_cfg.SPI_Wrapper_ref_vif;
				drv.seq_item_port.connect(sqr.seq_item_export);
			end
			mon.SPI_Wrapper_mon_vif = SPI_Wrapper_cfg.SPI_Wrapper_vif;
			mon.SPI_Wrapper_ref_mon_vif = SPI_Wrapper_cfg.SPI_Wrapper_ref_vif;
			mon.mon_ap.connect(agt_ap);
		endfunction : connect_phase
		
	endclass : SPI_Wrapper_agent
	
endpackage : SPI_Wrapper_agent_pkg