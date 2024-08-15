package slave_test_pkg;
import uvm_pkg::*;
import slave_env_pkg::*;
import slave_config_pkg::*;
import slave_sequence_pkg::*;
`include "uvm_macros.svh"

	class slave_test extends uvm_test;
		`uvm_component_utils(slave_test)

		slave_env env_s;
		slave_config slave_cfg;
		
		slave_reset_sequence reset_seq;
		slave_write_only_sequence write_only_seq;
		slave_read_only_sequence read_only_seq;
		slave_write_read_sequence write_read_seq;
		slave_main_sequence main_seq;
		

		function new(string name = "slave_test", uvm_component parent = null);
			super.new(name, parent);
		endfunction : new

		function void build_phase(uvm_phase phase);
			super.build_phase(phase);
			env_s = slave_env::type_id::create("env_s", this);
			slave_cfg = slave_config::type_id::create("slave_cfg", this);
			
			reset_seq 		= slave_reset_sequence::type_id::create("reset_seq", this);
			write_only_seq 	= slave_write_only_sequence::type_id::create("write_only_seq", this);
			read_only_seq 	= slave_read_only_sequence::type_id::create("read_only_seq", this);
			write_read_seq 	= slave_write_read_sequence::type_id::create("write_read_seq", this);
			main_seq 		= slave_main_sequence::type_id::create("main_seq", this);
			
			slave_cfg.active = UVM_ACTIVE;

			if(!uvm_config_db #(virtual slave_if)::get(this, "", "SLAVE_IF", slave_cfg.slave_vif))
				`uvm_fatal("build_phase", "Test - Unable to get the virtual interface of the Slave (DUT) from the uvm_config_db");

			if(!uvm_config_db #(virtual slave_ref_if)::get(this, "", "SLAVE_REF_IF", slave_cfg.slave_ref_vif))
				`uvm_fatal("build_phase", "Test - Unable to get the virtual interface of the Slave (REF) from the uvm_config_db");
			
			uvm_config_db #(slave_config)::set(this, "*", "SLAVE_CFG", slave_cfg);

			//set_report_verbosity_level_hier(UVM_HIGH);
		endfunction

		task run_phase(uvm_phase phase);
			super.run_phase(phase);
			phase.raise_objection(this);
			`uvm_info("run_phase", "Reset Asserted", UVM_LOW);
			reset_seq.start(env_s.agt.sqr);
			`uvm_info("run_phase", "Reset Deasserted", UVM_LOW);

			`uvm_info("run_phase", "Stimulus Generation Started", UVM_LOW);

			`uvm_info("run_phase", "Testing Write-Only Operations", UVM_LOW);
			write_only_seq.start(env_s.agt.sqr);

			`uvm_info("run_phase", "Testing Read-Only Operations", UVM_LOW);
			read_only_seq.start(env_s.agt.sqr);

			`uvm_info("run_phase", "Testing Write-Read Operations", UVM_LOW);
			write_read_seq.start(env_s.agt.sqr);

			`uvm_info("run_phase", "Main Sequence (Complete Randomization)", UVM_LOW);
			main_seq.start(env_s.agt.sqr);

			`uvm_info("run_phase", "Stimulus Generation Ended", UVM_LOW);
			phase.drop_objection(this);
		endtask : run_phase

	endclass : slave_test
	
endpackage : slave_test_pkg