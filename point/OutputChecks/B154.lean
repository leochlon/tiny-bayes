import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block154_checked : centerBlock 154 = true := by decide +kernel
#print axioms block154_checked
end PythiaCert.Output
