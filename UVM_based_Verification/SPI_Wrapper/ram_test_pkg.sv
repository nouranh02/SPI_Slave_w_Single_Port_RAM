package ram_test_pkg;
import uvm_pkg::*;
import ram_env_pkg::*;
import ram_config_pkg::*;
import ram_sequence_pkg::*;
`include "uvm_macros.svh"

	class ram_test extends uvm_test;
		`uvm_component_utils(ram_test)

		ram_env env_r;
		ram_config ram_cfg;

		ram_reset_sequence reset_seq;
		ram_write_only_sequence write_only_seq;
		ram_read_only_sequence read_only_seq;
		ram_write_read_sequence write_read_seq;
		main_sequence main_seq;

		function new(string name = "ram_test", uvm_component parent = null);
			super.new(name, parent);
		endfunction : new

		function void build_phase(uvm_phase phase);
			super.build_phase(phase);
			env_r = ram_env::type_id::create("env_r", this);
			ram_cfg = ram_config::type_id::create("ram_cfg", this);

			reset_seq 		= ram_reset_sequence::type_id::create("reset_seq", this);
			write_only_seq 	= ram_write_only_sequence::type_id::create("write_only_seq", this);
			read_only_seq 	= ram_read_only_sequence::type_id::create("read_only_seq", this);
			write_read_seq 	= ram_write_read_sequence::type_id::create("write_read_seq", this);
			main_seq 		= main_sequence::type_id::create("main_seq", this);

			ram_cfg.active = UVM_ACTIVE;

			if(!uvm_config_db #(virtual ram_if)::get(this, "", "RAM_IF", ram_cfg.ram_vif))
				`uvm_fatal("build_phase", "Test - Unable to get the virtual interface of the RAM (DUT) from the uvm_config_db");

			if(!uvm_config_db #(virtual ram_ref_if)::get(this, "", "RAM_REF_IF", ram_cfg.ram_ref_vif))
				`uvm_fatal("build_phase", "Test - Unable to get the virtual interface of the RAM (REF) from the uvm_config_db");

			uvm_config_db #(ram_config)::set(this, "*", "RAM_CFG", ram_cfg);

			//set_report_verbosity_level_hier(UVM_HIGH);
		endfunction

		task run_phase(uvm_phase phase);
			super.run_phase(phase);
			phase.raise_objection(this);
			`uvm_info("run_phase", "Reset Asserted", UVM_LOW);
			reset_seq.start(env_r.agt.sqr);
			`uvm_info("run_phase", "Reset Deasserted", UVM_LOW);

			`uvm_info("run_phase", "Stimulus Generation Started", UVM_LOW);

			`uvm_info("run_phase", "Testing Write-Only Operations", UVM_LOW);
			write_only_seq.start(env_r.agt.sqr);

			`uvm_info("run_phase", "Testing Read-Only Operations", UVM_LOW);
			read_only_seq.start(env_r.agt.sqr);

			`uvm_info("run_phase", "Testing Write-Read Operations", UVM_LOW);
			write_read_seq.start(env_r.agt.sqr);

			`uvm_info("run_phase", "Main Sequence (Complete Randomization)", UVM_LOW);
			write_read_seq.start(env_r.agt.sqr);

			`uvm_info("run_phase", "Stimulus Generation Ended", UVM_LOW);
			phase.drop_objection(this);
		endtask : run_phase

	endclass : ram_test
	
endpackage : ram_test_pkg