import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block128_checked : centerBlock 128 = true := by decide +kernel
#print axioms block128_checked
end PythiaCert.Output
