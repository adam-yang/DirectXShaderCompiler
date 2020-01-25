// RUN: %dxc -E main -T ps_6_6 %s -Od | FileCheck %s

// Test that non-const arithmetic are not optimized away

Texture2D tex0 : register(t0);
Texture2D tex1 : register(t1);

[RootSignature("DescriptorTable(SRV(t0), SRV(t1))")]
float4 main() : SV_Target {
  // CHECK: %[[preserve_i32:[0-9]+]] = load i32, i32* @dx.preserve.value
  // CHECK: %[[preserve_f32:[0-9]+]] = sitofp i32 %[[preserve_i32]]

  float x = 10;
  // fadd float 1.000000e+01, %[[preserve_f32]]

  float y = x + 5;
  // CHECK: %[[a1:.+]] = fadd
  // fadd float [[a1]], %[[preserve_f32]]

  float z = y * 2;
  // CHECK: %[[b1:.+]] = fmul
  // fadd float [[b1]], %[[preserve_f32]]

  float w = z / 0.5;
  // CHECK: %[[c1:.+]] = fdiv
  // fadd float [[c1]], %[[preserve_f32]]

  Texture2D tex = tex0; 
  // CHECK: load i32, i32* @dx.nothing

  // CHECK: br i1
  if (w >= 0) {
    tex = tex1;
    // CHECK: load i32, i32* @dx.nothing
    // CHECK: br
  }

  // CHECK: %[[d1:.+]] = fadd
  // CHECK: %[[d2:.+]] = fadd
  // CHECK: %[[d3:.+]] = fadd
  // CHECK: %[[d4:.+]] = fadd
  // fadd float [[d1]], %[[preserve_f32]]
  // fadd float [[d2]], %[[preserve_f32]]
  // fadd float [[d3]], %[[preserve_f32]]
  // fadd float [[d4]], %[[preserve_f32]]

  return tex.Load(0) + float4(x,y,z,w);
  // CHECK: load i32, i32* @dx.nothing
}

