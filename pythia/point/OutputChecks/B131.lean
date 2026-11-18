import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block131_checked : centerBlock 131 = true := by decide +kernel
#print axioms block131_checked
end PythiaCert.Output
