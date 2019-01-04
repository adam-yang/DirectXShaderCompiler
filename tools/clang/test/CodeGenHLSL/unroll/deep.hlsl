// RUN: %dxc -E main -T ps_6_0 %s | FileCheck %s

// CHECK: call i32 @dx.op.bufferUpdateCounter
// CHECK: call i32 @dx.op.bufferUpdateCounter
// CHECK: call i32 @dx.op.bufferUpdateCounter

// CHECK-NOT: call i32 @dx.op.bufferUpdateCounter

AppendStructuredBuffer<float> buf0;
AppendStructuredBuffer<float> buf1;
AppendStructuredBuffer<float> buf2;

uint g_cond;
uint g_cond2;

float main() : SV_Target {

  AppendStructuredBuffer<float> buf[3] = {
    buf0, buf1, buf2
  };

  [unroll]
  for (int i = 0; i < 3; i++) {
    if (i == g_cond) {
      if (i == g_cond2) {
        buf[i].Append(i*10);
        return 2;
      }
      return 1;
    }
  }
  
  return 0;
}

