import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block100_checked : centerBlock 100 = true := by decide +kernel
#print axioms block100_checked
end PythiaCert.Output
