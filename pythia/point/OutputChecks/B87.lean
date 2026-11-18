import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block87_checked : centerBlock 87 = true := by decide +kernel
#print axioms block87_checked
end PythiaCert.Output
