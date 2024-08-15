package ram_agent_pkg;
import uvm_pkg::*;
import ram_driver_pkg::*;
import ram_sequencer_pkg::*;
import ram_monitor_pkg::*;
import ram_config_pkg::*;
import ram_sequence_item_pkg::*;

`include "uvm_macros.svh"

	class ram_agent extends uvm_agent;
		`uvm_component_utils(ram_agent)

		ram_driver drv;
		ram_sequencer sqr;
		ram_monitor mon;
		ram_config ram_cfg;
		uvm_analysis_port #(ram_sequence_item) agt_ap;

		function new(string name = "ram_agent", uvm_component parent = null);
			super.new(name, parent);			
		endfunction : new

		function void build_phase(uvm_phase phase);
			super.build_phase(phase);
			ram_cfg = ram_config::type_id::create("ram_cfg", this);
			if(!uvm_config_db#(ram_config)::get(this, "", "RAM_CFG", ram_cfg))
				`uvm_fatal("build_phase", "Agent - Unable to get RAM Configuration Object.");

			if(ram_cfg.active) begin
				drv = ram_driver::type_id::create("drv", this);
				sqr = ram_sequencer::type_id::create("sqr", this);
			end
			mon = ram_monitor::type_id::create("mon", this);

			agt_ap = new("agt_ap", this);
		endfunction : build_phase

		function void connect_phase(uvm_phase phase);
			super.connect_phase(phase);
			if(ram_cfg.active) begin
				drv.ram_drv_vif = ram_cfg.ram_vif;
				drv.ram_ref_drv_vif = ram_cfg.ram_ref_vif;
				drv.seq_item_port.connect(sqr.seq_item_export);
			end
			mon.ram_mon_vif = ram_cfg.ram_vif;
			mon.ram_ref_mon_vif = ram_cfg.ram_ref_vif;
			mon.mon_ap.connect(agt_ap);
		endfunction : connect_phase
		
	endclass : ram_agent
	
endpackage : ram_agent_pkg