// RUN: %dxc -E main -T ps_6_0 %s -resource-binding-file resource_binding.txt

cbuffer cb {
  float a;
};
cbuffer cb_2 {
  float b;
};

SamplerState samp0;
Texture2D texture_0;
RWTexture1D<float> uav_0;

[RootSignature("CBV(b10,space=30), CBV(b42,space=999), DescriptorTable(Sampler(s1,space=2)), DescriptorTable(SRV(t1,space=2)), DescriptorTable(UAV(u1,space=2))")]
float main(float2 uv : UV, uint i : I) :SV_Target {
  return a + b + texture_0.Sample(samp0, uv).r + uav_0[i];
}