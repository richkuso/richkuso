// SystemVerilog Counter Module
module counter #(
    parameter WIDTH = 8
)(
    input  logic             clk,
    input  logic             rst_n,
    input  logic             enable,
    input  logic             load,
    input  logic [WIDTH-1:0] load_data,
    output logic [WIDTH-1:0] count,
    output logic             overflow
);

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            count <= '0;
            overflow <= 1'b0;
        end
        else if (load) begin
            count <= load_data;
            overflow <= 1'b0;
        end
        else if (enable) begin
            {overflow, count} <= count + 1'b1;
        end
    end

endmodule