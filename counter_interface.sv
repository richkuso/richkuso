// SystemVerilog Interface for Counter
interface counter_if #(parameter WIDTH = 8) (input logic clk);
    
    // Signals
    logic             rst_n;
    logic             enable;
    logic             load;
    logic [WIDTH-1:0] load_data;
    logic [WIDTH-1:0] count;
    logic             overflow;
    
    // Clocking blocks for different agents
    clocking driver_cb @(posedge clk);
        default input #1 output #1;
        output rst_n, enable, load, load_data;
        input  count, overflow;
    endclocking
    
    clocking monitor_cb @(posedge clk);
        default input #1;
        input rst_n, enable, load, load_data, count, overflow;
    endclocking
    
    // Modports
    modport DUT (
        input  clk, rst_n, enable, load, load_data,
        output count, overflow
    );
    
    modport DRIVER (
        clocking driver_cb,
        input clk
    );
    
    modport MONITOR (
        clocking monitor_cb,
        input clk
    );
    
    // Assertions
    property p_reset_behavior;
        @(posedge clk) !rst_n |-> ##1 (count == 0 && overflow == 0);
    endproperty
    
    property p_load_behavior;
        @(posedge clk) rst_n && load |-> ##1 count == $past(load_data);
    endproperty
    
    assert property (p_reset_behavior) else $error("Reset behavior violation");
    assert property (p_load_behavior) else $error("Load behavior violation");
    
endinterface