// RUN: %dxc -E main -T ps_6_0 %s | FileCheck %s

// CHECK: call float @dx.op.dot3
// CHECK-NOT: call float @dx.op.dot3

uint g_cond;
uint g_cond2;

float main(float3 a : A, float3 b : B) : SV_Target {

  float result = 0;

  [unroll]
  for (int i = 0; i < 3; i++) {
    if (i == g_cond) {
      if (i == g_cond2) {
        result += dot(a*i, b);
        return result;
      }
      return result;
    }
  }
  
  return result;
}

