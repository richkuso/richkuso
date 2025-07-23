module testbench;
  import uvm_pkg::*;
  import uvm_agent_pkg::*;
  `include "uvm_macros.svh"
  
  // Clock and reset generation
  logic clk = 0;
  logic reset = 1;
  
  always #5 clk = ~clk; // 100MHz clock
  
  initial begin
    reset = 1;
    #100;
    reset = 0;
  end
  
  // Interface instantiation
  my_interface intf(clk, reset);
  
  // Simple DUT (Design Under Test) for demonstration
  simple_dut dut (
    .clk(clk),
    .reset(reset),
    .data(intf.data),
    .addr(intf.addr),
    .read_write(intf.read_write),
    .valid(intf.valid),
    .ready(intf.ready)
  );
  
  // UVM Test Class
  class my_test extends uvm_test;
    `uvm_component_utils(my_test)
    
    my_agent agent;
    
    function new(string name = "my_test", uvm_component parent = null);
      super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      
      // Create agent
      agent = my_agent::type_id::create("agent", this);
      
      // Configure the agent as active
      uvm_config_db#(uvm_active_passive_enum)::set(this, "agent", "is_active", UVM_ACTIVE);
      
      // Set the virtual interface
      uvm_config_db#(virtual my_interface)::set(this, "agent.*", "vif", intf);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
      my_sequence seq;
      
      phase.raise_objection(this);
      
      `uvm_info("TEST", "Starting test sequence", UVM_LOW)
      
      seq = my_sequence::type_id::create("seq");
      seq.start(agent.sequencer);
      
      #1000; // Wait for some time
      
      `uvm_info("TEST", "Test completed", UVM_LOW)
      
      phase.drop_objection(this);
    endtask
  endclass
  
  // Initial block to start UVM
  initial begin
    // Set up UVM configuration
    uvm_config_db#(virtual my_interface)::set(null, "*", "vif", intf);
    
    // Run the test
    run_test("my_test");
  end
  
  // Waveform dumping
  initial begin
    $dumpfile("waves.vcd");
    $dumpvars(0, testbench);
  end
  
endmodule

// Simple DUT for demonstration
module simple_dut (
  input  logic        clk,
  input  logic        reset,
  input  logic [31:0] data,
  input  logic [7:0]  addr,
  input  logic        read_write,
  input  logic        valid,
  output logic        ready
);
  
  // Simple memory array
  logic [31:0] memory [0:255];
  
  // State machine
  typedef enum logic [1:0] {
    IDLE,
    PROCESSING,
    DONE
  } state_t;
  
  state_t current_state, next_state;
  
  // State register
  always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
      current_state <= IDLE;
    end else begin
      current_state <= next_state;
    end
  end
  
  // Next state logic
  always_comb begin
    next_state = current_state;
    ready = 1'b0;
    
    case (current_state)
      IDLE: begin
        if (valid) begin
          next_state = PROCESSING;
        end
      end
      
      PROCESSING: begin
        next_state = DONE;
      end
      
      DONE: begin
        ready = 1'b1;
        next_state = IDLE;
      end
    endcase
  end
  
  // Memory operations
  always_ff @(posedge clk) begin
    if (current_state == PROCESSING) begin
      if (read_write) begin
        memory[addr] <= data;
        $display("DUT: Write addr=0x%0h, data=0x%0h", addr, data);
      end else begin
        $display("DUT: Read addr=0x%0h, data=0x%0h", addr, memory[addr]);
      end
    end
  end
  
endmodule