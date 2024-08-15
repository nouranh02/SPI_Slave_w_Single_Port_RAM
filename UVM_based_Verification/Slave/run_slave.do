vlib work
vlog -f src_files_slave.list +define+SIM +cover
vsim -voptargs=+acc work.slave_top -classdebug -uvmcontrol=all -cover
add wave /slave_top/slaveif/*
add wave -position insertpoint \
sim:/slave_top/slaverefif/MISO_ref \
sim:/slave_top/slaverefif/rx_valid_ref \
sim:/slave_top/slaverefif/rx_data_ref
run 0
#add wave -position insertpoint  \
#sim:/uvm_root/uvm_test_top/env_s/agt/drv/stim_seq_item
#add wave -position insertpoint  \
#sim:/uvm_root/uvm_test_top/env_s/agt/drv/stim_seq_item.signal
#sim:/uvm_root/uvm_test_top/env_s/agt/drv/stim_seq_item.signal_old
add wave -position insertpoint  \
sim:/uvm_root/uvm_test_top/env_s/sb/correct_count_MISO \
sim:/uvm_root/uvm_test_top/env_s/sb/error_count_MISO \
sim:/uvm_root/uvm_test_top/env_s/sb/correct_count_rxvalid \
sim:/uvm_root/uvm_test_top/env_s/sb/error_count_rxvalid \
sim:/uvm_root/uvm_test_top/env_s/sb/correct_count_rxdata \
sim:/uvm_root/uvm_test_top/env_s/sb/error_count_rxdata

add wave /slave_top/DUT/assertion_reset_asserted /slave_top/DUT/assertion_SS_inactive /slave_top/DUT/assertion_CHK_first /slave_top/DUT/assertion_CHK_WR /slave_top/DUT/assertion_CHK_RD /slave_top/DUT/assertion_MOSI_wr /slave_top/DUT/assertion_MOSI_rd /slave_top/DUT/assertion_MOSI_rd_add /slave_top/DUT/assertion_MOSI_rd_data /slave_top/DUT/assertion_no_add_add /slave_top/DUT/assertion_no_data_data /slave_top/DUT/assertion_rx_wr /slave_top/DUT/assertion_rx_rd_add /slave_top/DUT/assertion_rx_rd_data /slave_top/DUT/assertion_rx_tx /slave_top/DUT/assertion_rx_chk /slave_top/DUT/assertion_MISO_rd_only

coverage save slave_top.ucdb -onexit
run -all

#quit -sim
#vcover report slave_top.ucdb -details -annotate -all -output Slave_Coverage.txt