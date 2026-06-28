#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
根图分析 - RootVision
Entry point
"""
import sys
import os
import multiprocessing

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from rootvision.utils import check_python_version, check_dependencies


def main():
    if sys.platform.startswith('win'):
        multiprocessing.freeze_support()
    else:
        multiprocessing.set_start_method('spawn', force=True)

    check_python_version()

    python_version = sys.version_info
    print(f"Python版本: {python_version.major}.{python_version.minor}.{python_version.micro}")
    print(f"CPU核心数: {multiprocessing.cpu_count()}")
    print(f"并行处理超时时间: 660秒")
    print(f"并行处理上限: 5张图片")
    print(f"扫描图像优化: 已集成")

    missing_libs = check_dependencies()
    if missing_libs:
        print(f"缺少必要的库: {', '.join(missing_libs)}")
        print("请运行: pip install " + " ".join(missing_libs))
        try:
            import tkinter as tk
            from tkinter import messagebox
            error_root = tk.Tk()
            error_root.withdraw()
            messagebox.showerror(
                "缺少依赖库",
                f"缺少以下必要的Python库:\n\n{', '.join(missing_libs)}\n\n"
                f"请运行安装脚本:\n\npip install {' '.join(missing_libs)}"
            )
            error_root.destroy()
        except Exception:
            pass
        sys.exit(1)

    print("所有依赖库已成功导入:")

    from rootvision.gui import RootAnalysisApp

    root = tk.Tk()
    app = RootAnalysisApp(root)

    def on_closing():
        app.save_config()
        root.destroy()

    root.protocol("WM_DELETE_WINDOW", on_closing)
    root.mainloop()


if __name__ == "__main__":
    main()
