import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block190_checked : centerBlock 190 = true := by decide +kernel
#print axioms block190_checked
end PythiaCert.Output
