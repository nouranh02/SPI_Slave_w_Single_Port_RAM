package shared_pkg;

typedef enum logic [2:0] {IDLE, READ_DATA, READ_ADD, CHK_CMD, WRITE, WAIT_WR, WAIT_RD, WAIT_RD2} state_e;
typedef enum bit [1:0] {STORE_WR_ADDR, WRITE_DATA, STORE_RD_ADDR, READ_DATA_} signal_e;

parameter ADDR_SIZE = 8;

parameter ALL_ONES = (2**ADDR_SIZE) - 1;;
parameter ZERO = 0;

endpackage : shared_pkg