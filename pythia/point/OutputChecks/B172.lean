import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block172_checked : centerBlock 172 = true := by decide +kernel
#print axioms block172_checked
end PythiaCert.Output
