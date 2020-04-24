// RUN: %dxc -E main -T ps_6_0 -Zi %s | FileCheck %s

// Test that the debug information for the result of a texture load
// is preserved after scalarization and optims.

// CHECK: call %dx.types.ResRet.f32 @dx.op.textureLoad.f32
// CHECK-DAG: call void @llvm.dbg.value
// CHECK-DAG: extractvalue %dx.types.ResRet.f32
// CHECK-DAG: extractvalue %dx.types.ResRet.f32
// CHECK: call void @dx.op.storeOutput.f32
// CHECK: call void @dx.op.storeOutput.f32

Texture1D<float2> tex;
float2 main() : SV_Target
{
    float2 texel = tex.Load(0);
    return texel;
}
