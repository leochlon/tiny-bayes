import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block136_checked : centerBlock 136 = true := by decide +kernel
#print axioms block136_checked
end PythiaCert.Output
