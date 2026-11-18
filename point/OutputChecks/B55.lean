import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block55_checked : centerBlock 55 = true := by decide +kernel
#print axioms block55_checked
end PythiaCert.Output
