package slave_agent_pkg;
import uvm_pkg::*;
import slave_driver_pkg::*;
import slave_sequencer_pkg::*;
import slave_monitor_pkg::*;
import slave_config_pkg::*;
import slave_sequence_item_pkg::*;

`include "uvm_macros.svh"

	class slave_agent extends uvm_agent;
		`uvm_component_utils(slave_agent)

		slave_driver drv;
		slave_sequencer sqr;
		slave_monitor mon;
		slave_config slave_cfg;
		uvm_analysis_port #(slave_sequence_item) agt_ap;

		function new(string name = "slave_agent", uvm_component parent = null);
			super.new(name, parent);			
		endfunction : new

		function void build_phase(uvm_phase phase);
			super.build_phase(phase);
			slave_cfg = slave_config::type_id::create("slave_cfg", this);
			if(!uvm_config_db#(slave_config)::get(this, "", "SLAVE_CFG", slave_cfg))
				`uvm_fatal("build_phase", "Agent - Unable to get Slave Configuration Object.");

			if(slave_cfg.active) begin
				drv = slave_driver::type_id::create("drv", this);
				sqr = slave_sequencer::type_id::create("sqr", this);
			end
			mon = slave_monitor::type_id::create("mon", this);

			agt_ap = new("agt_ap", this);
		endfunction : build_phase

		function void connect_phase(uvm_phase phase);
			super.connect_phase(phase);
			if(slave_cfg.active) begin
				drv.slave_drv_vif = slave_cfg.slave_vif;
				drv.slave_ref_drv_vif = slave_cfg.slave_ref_vif;
				drv.seq_item_port.connect(sqr.seq_item_export);
			end
			mon.slave_mon_vif = slave_cfg.slave_vif;
			mon.slave_ref_mon_vif = slave_cfg.slave_ref_vif;
			mon.mon_ap.connect(agt_ap);
		endfunction : connect_phase
		
	endclass : slave_agent
	
endpackage : slave_agent_pkg