A parameterizable floating point operations (written in Verilog)

Implemented operations:
1) Multiplication
2) Addition
3) Conversion (real-to-integer)
4) Conversion (integer-to-real)
5) Absolute Value
6) Comparison
7) Complex Multiplication
8) Complex Addition
9) Complex Conjugation

#### Parameters

* `NUM_W`   - Number Width
* `EXP_W`   - Exponent Width
* `MAN_W`   - Mantissa Width
* `TRIGOUT` - Output Trigger (1 - enable, 0 - disable)

#### IEEE754 settings

*	FP16 : `NUM_W` = 16,  `EXP_W` = 5,  `MAN_W` = 10  (Half-precision)
*	FP32 : `NUM_W` = 32,  `EXP_W` = 8,  `MAN_W` = 23  (Single-precision)
*	FP64 : `NUM_W` = 64,  `EXP_W` = 11, `MAN_W` = 52  (Double-precision)
*	FP128: `NUM_W` = 128, `EXP_W` = 15, `MAN_W` = 112 (Quadruple-precision)
*	FP256: `NUM_W` = 256, `EXP_W` = 19, `MAN_W` = 236 (Octuple-precision)

##### Note: It is able to use any custom values for Exponent and Mantissa Width.
