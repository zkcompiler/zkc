module

public import Zkc.Applications.Clean.NativeClients

@[expose] public section

/-- Regenerate the optional native-adapter source fixtures. -/
def main := CleanExamples.NativeClients.run
