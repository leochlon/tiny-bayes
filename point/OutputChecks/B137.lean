import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block137_checked : centerBlock 137 = true := by decide +kernel
#print axioms block137_checked
end PythiaCert.Output
