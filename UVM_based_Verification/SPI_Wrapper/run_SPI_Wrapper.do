vlib work
vlog -f src_files_SPI_Wrapper.list +define+SIM +cover
vsim -voptargs=+acc work.SPI_Wrapper_top -classdebug -uvmcontrol=all -cover
add wave /SPI_Wrapper_top/SPI_Wrapperif/*
add wave /SPI_Wrapper_top/SPI_Wrapper_refif/MISO_ref
add wave -position insertpoint \
sim:/SPI_Wrapper_top/slaveif/tx_data \
sim:/SPI_Wrapper_top/slaveif/tx_valid \
sim:/SPI_Wrapper_top/slaveif/rx_valid \
sim:/SPI_Wrapper_top/slaveif/rx_data
add wave -position insertpoint  \
sim:/SPI_Wrapper_top/ramDUT/mem
run 0
#add wave -position insertpoint  \
#sim:/uvm_root/uvm_test_top/env/agt/drv/stim_seq_item
#add wave -position insertpoint  \
#sim:/shared_pkg::temp_txn_wr_add \
#sim:/shared_pkg::temp_txn_wr_data \
#sim:/shared_pkg::temp_txn_rd_add \
#sim:/shared_pkg::temp_txn_rd_data
add wave -position insertpoint  \
sim:/uvm_root/uvm_test_top/env/sb/correct_count \
sim:/uvm_root/uvm_test_top/env/sb/error_count
add wave -position insertpoint  \
sim:/uvm_root/uvm_test_top/env_s/sb/correct_count_MISO \
sim:/uvm_root/uvm_test_top/env_s/sb/error_count_MISO \
sim:/uvm_root/uvm_test_top/env_s/sb/correct_count_rxvalid \
sim:/uvm_root/uvm_test_top/env_s/sb/error_count_rxvalid \
sim:/uvm_root/uvm_test_top/env_s/sb/correct_count_rxdata \
sim:/uvm_root/uvm_test_top/env_s/sb/error_count_rxdata
add wave -position insertpoint  \
sim:/uvm_root/uvm_test_top/env_r/sb/correct_count_tx \
sim:/uvm_root/uvm_test_top/env_r/sb/error_count_tx \
sim:/uvm_root/uvm_test_top/env_r/sb/correct_count_dout \
sim:/uvm_root/uvm_test_top/env_r/sb/error_count_dout

add wave /SPI_Wrapper_top/SPI_WrapperDUT/assertion_reset_asserted /SPI_Wrapper_top/SPI_WrapperDUT/assertion_SS_inactive /SPI_Wrapper_top/SPI_WrapperDUT/assertion_tx_inactive /SPI_Wrapper_top/SPI_WrapperDUT/assertion_MISO_out
add wave /SPI_Wrapper_top/ramDUT/assertion_save_wr /SPI_Wrapper_top/ramDUT/assertion_wr_d /SPI_Wrapper_top/ramDUT/assertion_save_rd /SPI_Wrapper_top/ramDUT/assertion_rd_d /SPI_Wrapper_top/ramDUT/assertion_tx_a /SPI_Wrapper_top/ramDUT/assertion_tx_in

coverage save SPI_Wrapper_top.ucdb -onexit
run -all

#quit -sim
#vcover report SPI_Wrapper_top.ucdb -details -annotate -all -output SPI_Wrapper_Coverage.txt