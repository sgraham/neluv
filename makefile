all: luv_lark.py
	@python main.py | C:\Users\sgraham\Sync\utils\clang-format\clang-format.exe -style=Chromium

luv_lark.py: luv.lark
	python -m lark.tools.standalone luv.lark >luv_lark.py
