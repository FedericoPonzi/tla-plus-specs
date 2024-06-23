---- ---- MODULE Common ----
EXTENDS TLC

StatusInitial == "Initial"
StatusReading == "Reading"
StatusWriting == "Writing"
StatusCompleted == "Completed"
StatusAborted == "Aborted"
StatusType == {StatusInitial, StatusReading, StatusWriting, StatusCompleted, StatusAborted}

====
