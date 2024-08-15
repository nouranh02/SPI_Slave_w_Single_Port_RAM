vlib work
vlog -f src_files_ram.list +define+SIM +cover
vsim -voptargs=+acc work.ram_top -classdebug -uvmcontrol=all -cover
add wave /ram_top/ramif/*
add wave -position insertpoint  \
sim:/ram_top/ram_refif/dout_ref \
sim:/ram_top/ram_refif/tx_valid_ref
add wave -position insertpoint  \
sim:/ram_top/REF/signal \
sim:/ram_top/REF/data
add wave -position insertpoint  \
sim:/ram_top/DUT/write_addr \
sim:/ram_top/DUT/read_addr \
sim:/ram_top/DUT/mem
run 0
#add wave -position insertpoint  \
#sim:/uvm_root/uvm_test_top/env_r/agt/drv/stim_seq_item
add wave -position insertpoint  \
sim:/uvm_root/uvm_test_top/env_r/sb/correct_count_dout \
sim:/uvm_root/uvm_test_top/env_r/sb/error_count_dout \
sim:/uvm_root/uvm_test_top/env_r/sb/correct_count_tx \
sim:/uvm_root/uvm_test_top/env_r/sb/error_count_tx
add wave /ram_top/DUT/assertion_reset /ram_top/DUT/assertion_rx_inv /ram_top/DUT/assertion_save_wr /ram_top/DUT/assertion_wr_d /ram_top/DUT/assertion_save_rd /ram_top/DUT/assertion_rd_d /ram_top/DUT/assertion_tx_a /ram_top/DUT/assertion_tx_in

coverage save ram_top.ucdb -onexit
run -all

#quit -sim
#vcover report ram_top.ucdb -details -annotate -all -output RAM_Coverage.txt