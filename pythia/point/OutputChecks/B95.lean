import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block95_checked : centerBlock 95 = true := by decide +kernel
#print axioms block95_checked
end PythiaCert.Output
