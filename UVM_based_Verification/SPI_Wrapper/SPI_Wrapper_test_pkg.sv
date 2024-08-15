package SPI_Wrapper_test_pkg;
import uvm_pkg::*;
import SPI_Wrapper_env_pkg::*;
import slave_env_pkg::*;
import ram_env_pkg::*;
import SPI_Wrapper_config_pkg::*;
import slave_config_pkg::*;
import ram_config_pkg::*;
import SPI_Wrapper_sequence_pkg::*;
`include "uvm_macros.svh"

	class SPI_Wrapper_test extends uvm_test;
		`uvm_component_utils(SPI_Wrapper_test)

		SPI_Wrapper_env env;
		slave_env env_s;
		ram_env env_r;

		SPI_Wrapper_config SPI_Wrapper_cfg;
		slave_config slave_cfg;
		ram_config ram_cfg;
		
		SPI_Wrapper_reset_sequence reset_seq;
		SPI_Wrapper_write_only_sequence write_only_seq;
		SPI_Wrapper_read_only_sequence read_only_seq;
		SPI_Wrapper_write_read_sequence write_read_seq;
		SPI_Wrapper_main_sequence main_seq;
		

		function new(string name = "SPI_Wrapper_test", uvm_component parent = null);
			super.new(name, parent);
		endfunction : new

		function void build_phase(uvm_phase phase);
			super.build_phase(phase);
			env = SPI_Wrapper_env::type_id::create("env", this);
			env_s = slave_env::type_id::create("env_s", this);
			env_r = ram_env::type_id::create("env_r", this);

			SPI_Wrapper_cfg = SPI_Wrapper_config::type_id::create("SPI_Wrapper_cfg", this);
			slave_cfg = slave_config::type_id::create("slave_cfg", this);
			ram_cfg = ram_config::type_id::create("ram_cfg", this);
			
			reset_seq 		= SPI_Wrapper_reset_sequence::type_id::create("reset_seq", this);
			write_only_seq 	= SPI_Wrapper_write_only_sequence::type_id::create("write_only_seq", this);
			read_only_seq 	= SPI_Wrapper_read_only_sequence::type_id::create("read_only_seq", this);
			write_read_seq 	= SPI_Wrapper_write_read_sequence::type_id::create("write_read_seq", this);
			main_seq 		= SPI_Wrapper_main_sequence::type_id::create("main_seq", this);
			
			SPI_Wrapper_cfg.active = UVM_ACTIVE;
			slave_cfg.active = UVM_PASSIVE;
			ram_cfg.active = UVM_PASSIVE;

			if(!uvm_config_db #(virtual SPI_Wrapper_if)::get(this, "", "SPI_Wrapper_IF", SPI_Wrapper_cfg.SPI_Wrapper_vif))
				`uvm_fatal("build_phase", "Test - Unable to get the virtual interface of the SPI_Wrapper (DUT) from the uvm_config_db");

			if(!uvm_config_db #(virtual SPI_Wrapper_ref_if)::get(this, "", "SPI_Wrapper_REF_IF", SPI_Wrapper_cfg.SPI_Wrapper_ref_vif))
				`uvm_fatal("build_phase", "Test - Unable to get the virtual interface of the SPI_Wrapper (REF) from the uvm_config_db");

			if(!uvm_config_db #(virtual slave_if)::get(this, "", "SLAVE_IF", slave_cfg.slave_vif))
				`uvm_fatal("build_phase", "Test - Unable to get the virtual interface of the Slave (DUT) from the uvm_config_db");

			if(!uvm_config_db #(virtual slave_ref_if)::get(this, "", "SLAVE_REF_IF", slave_cfg.slave_ref_vif))
				`uvm_fatal("build_phase", "Test - Unable to get the virtual interface of the Slave (REF) from the uvm_config_db");

			if(!uvm_config_db #(virtual ram_if)::get(this, "", "RAM_IF", ram_cfg.ram_vif))
				`uvm_fatal("build_phase", "Test - Unable to get the virtual interface of the RAM (DUT) from the uvm_config_db");

			if(!uvm_config_db #(virtual ram_ref_if)::get(this, "", "RAM_REF_IF", ram_cfg.ram_ref_vif))
				`uvm_fatal("build_phase", "Test - Unable to get the virtual interface of the RAM (REF) from the uvm_config_db");
			
			uvm_config_db #(SPI_Wrapper_config)::set(this, "env*", "SPI_Wrapper_CFG", SPI_Wrapper_cfg);
			uvm_config_db #(slave_config)::set(this, "env_s*", "SLAVE_CFG", slave_cfg);
			uvm_config_db #(ram_config)::set(this, "env_r*", "RAM_CFG", ram_cfg);

			//set_report_verbosity_level_hier(UVM_HIGH);
		endfunction

		task run_phase(uvm_phase phase);
			super.run_phase(phase);
			phase.raise_objection(this);
			`uvm_info("run_phase", "Reset Asserted", UVM_LOW);
			reset_seq.start(env.agt.sqr);
			`uvm_info("run_phase", "Reset Deasserted", UVM_LOW);

			`uvm_info("run_phase", "Stimulus Generation Started", UVM_LOW);

			`uvm_info("run_phase", "Testing Write-Only Operations", UVM_LOW);
			write_only_seq.start(env.agt.sqr);

			`uvm_info("run_phase", "Testing Read-Only Operations", UVM_LOW);
			read_only_seq.start(env.agt.sqr);

			`uvm_info("run_phase", "Testing Write-Read Operations", UVM_LOW);
			write_read_seq.start(env.agt.sqr);

			`uvm_info("run_phase", "Main Sequence (Complete Randomization)", UVM_LOW);
			main_seq.start(env.agt.sqr);

			`uvm_info("run_phase", "Stimulus Generation Ended", UVM_LOW);
			phase.drop_objection(this);
		endtask : run_phase

	endclass : SPI_Wrapper_test
	
endpackage : SPI_Wrapper_test_pkg