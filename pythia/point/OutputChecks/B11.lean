import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block11_checked : centerBlock 11 = true := by decide +kernel
#print axioms block11_checked
end PythiaCert.Output
